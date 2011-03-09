import py
from pypy.rlib.parsing.ebnfparse import parse_ebnf
from pypy.rlib.parsing.regexparse import parse_regex
from pypy.rlib.parsing.lexer import Lexer, DummyLexer
from pypy.rlib.parsing.deterministic import DFA
from pypy.rlib.parsing.tree import Nonterminal, Symbol, RPythonVisitor
from pypy.rlib.parsing.parsing import PackratParser, LazyParseTable, Rule
from pypy.rlib.parsing.regex import StringExpression
from pypy.objspace.std.strutil import string_to_int, ParseStringOverflowError
from pypy.rlib.rarithmetic import ovfcheck
from pypy.rlib.rbigint import rbigint
from prolog.interpreter.continuation import Engine
from prolog.interpreter.module import Module

def make_regexes():
    regexs = [
        ("VAR", parse_regex("[A-Z_]([a-zA-Z0-9]|_)*|_")),
        ("NUMBER", parse_regex("(0|[1-9][0-9]*)(\.[0-9]+)?")),
        ("IGNORE", parse_regex(
            "[ \\n\\t]|(/\\*[^\\*]*(\\*[^/][^\\*]*)*\\*/)|(%[^\\n]*)")),
        ("ATOM", parse_regex("([a-z]([a-zA-Z0-9]|_)*)|('[^']*')|\[\]|!|\+|\-|\{\}")),
        ("STRING", parse_regex('"[^"]*"')),
        ("(", parse_regex("\(")),
        (")", parse_regex("\)")),
        ("[", parse_regex("\[")),
        ("]", parse_regex("\]")),
        ("{", parse_regex("\{")),
        ("}", parse_regex("\}")),
        (".", parse_regex("\.")),
        ("|", parse_regex("\|")),
    ]
    return zip(*regexs)

basic_rules = [
    Rule('query', [['toplevel_op_expr', '.', 'EOF']]),
    Rule('fact', [['toplevel_op_expr', '.']]),
    Rule('complexterm', [['ATOM', '(', 'toplevel_op_expr', ')'], ['expr']]),
    Rule('expr',
         [['VAR'],
          ['NUMBER'],
          ['+', 'NUMBER'],
          ['-', 'NUMBER'],
          ['ATOM'],
          ['STRING'],
          ['(', 'toplevel_op_expr', ')'],
          ['{', 'toplevel_op_expr', '}'],
          ['listexpr'],
          ]),
    Rule('listexpr', [['[', 'listbody', ']']]),
    Rule('listbody',
         [['toplevel_op_expr', '|', 'toplevel_op_expr'],
          ['toplevel_op_expr']])
    ]

# x: term with priority lower than f
# y: term with priority lower or equal than f
# possible types: xf yf xfx xfy yfx yfy fy fx
# priorities: A > B
#
# binaryops
# (1)  xfx:  A -> B f B | B
# (2)  xfy:  A -> B f A | B
# (3)  yfx:  A -> A f B | B
# (4)  yfy:  A -> A f A | B
#
# unaryops
# (5)  fx:   A -> f A | B
# (6)  fy:   A -> f B | B
# (7)  xf:   A -> B f | B
# (8)  yf:   A -> A f | B

def make_default_operations():
    operations = [
         (1200, [("xfx", ["-->", ":-"]),
                 ("fx",  [":-", "?-"])]),
         (1100, [("xfy", [";"])]),
         (1050, [("xfy", ["->"])]),
         (1000, [("xfy", [","])]),
         (900,  [("fy",  ["\\+"]),
                 ("fx",  ["~"])]),
         (700,  [("xfx", ["<", "=", "=..", "=@=", "=:=", "=<", "==", "=\=", ">",
                          ">=", "@<", "@=<", "@>", "@>=", "\=", "\==", "is"])]),
         (600,  [("xfy", [":"])]),
         (500,  [("yfx", ["+", "-", "/\\", "\\/", "xor"]),
                 ( "fx", ["+", "-", "?", "\\"])]),
         (400,  [("yfx", ["*", "/", "//", "<<", ">>", "mod", "rem"])]),
         (200,  [("xfx", ["**"]), ("xfy", ["^"])]),
         ]
    return operations

default_operations = make_default_operations()

import sys
sys.setrecursionlimit(10000)

def make_from_form(form, op, x, y):
    result = []
    for c in form:
        if c == 'x':
            result.append(x)
        if c == 'y':
            result.append(y)
        if c == 'f':
            result.append(op)
    return result

def make_expansion(y, x, allops):
    expansions = []
    for form, ops in allops:
        for op in ops:
            expansion = make_from_form(form, op, x, y)
            expansions.append(expansion)
    expansions.append([x])
    return expansions

def eliminate_immediate_left_recursion(symbol, expansions):
    newsymbol = "extra%s" % (symbol, )
    newexpansions = []
    with_recursion = [expansion for expansion in expansions
                          if expansion[0] == symbol]
    without_recursion = [expansion for expansion in expansions
                              if expansion[0] != symbol]
    expansions = [expansion + [newsymbol] for expansion in without_recursion]
    newexpansions = [expansion[1:] + [newsymbol]
                         for expansion in with_recursion]
    newexpansions.append([])
    return expansions, newexpansions, newsymbol

def make_all_rules(standard_rules, operations=None):
    if operations is None:
        operations = default_operations
    all_rules = standard_rules[:]
    for i in range(len(operations)):
        precedence, allops = operations[i]
        if i == 0:
            y = "toplevel_op_expr"
        else:
            y = "expr%s" % (precedence, )
        if i != len(operations) - 1:
            x = "expr%s" % (operations[i + 1][0], )
        else:
            x = "complexterm"
        expansions = make_expansion(y, x, allops)
        tup = eliminate_immediate_left_recursion(y, expansions)
        expansions, extra_expansions, extra_symbol = tup
        all_rules.append(Rule(extra_symbol, extra_expansions))
        all_rules.append(Rule(y, expansions))
    return all_rules

def add_necessary_regexs(regexs, names, operations=None):
    if operations is None:
        operations = default_operations
    regexs = regexs[:]
    names = names[:]
    for precedence, allops in operations:
        for form, ops in allops:
            for op in ops:
                regexs.insert(-1, StringExpression(op))
                names.insert(-1, "ATOM")
    return regexs, names

class PrologParseTable(LazyParseTable):
    def terminal_equality(self, symbol, input):
        if input.name == "ATOM":
            return symbol == "ATOM" or symbol == input.source
        return symbol == input.name
    def match_symbol(self, i, symbol):
        return LazyParseTable.match_symbol(self, i, symbol)

class PrologPackratParser(PackratParser):
    def __init__(self, rules, startsymbol):
        PackratParser.__init__(self, rules, startsymbol, PrologParseTable,
                               check_for_left_recursion=False)

def make_basic_rules():
    names, regexs = make_regexes()
    return basic_rules, names, regexs

def make_parser(basic_rules, names, regexs):
    real_rules = make_all_rules(basic_rules)
#    for r in real_rules:
#        print r
    regexs, names = add_necessary_regexs(list(regexs), list(names))
    lexer = Lexer(regexs, names, ignore=["IGNORE"])
    parser_fact = PrologPackratParser(real_rules, "fact")
    parser_query = PrologPackratParser(real_rules, "query")
    return lexer, parser_fact, parser_query, basic_rules

def make_all():
    return make_parser(*make_basic_rules())

def make_parser_at_runtime(operations):
    real_rules = make_all_rules(basic_rules, operations)
    parser_fact = PrologPackratParser(real_rules, "fact")
    return parser_fact

def _dummyfunc(arg, tree):
    return parser_fact

def parse_file(s, parser=None, callback=_dummyfunc, arg=None):
    tokens = lexer.tokenize(s)
    lines = []
    line = []
    for tok in tokens:
        line.append(tok)
        if tok.name== ".":
            lines.append(line)
            line = []
    if parser is None:
        parser = parser_fact
    trees = []
    for line in lines:
        tree = parser.parse(line, lazy=False)
        if callback is not None:
            # XXX ugh
            parser = callback(arg, tree)
            if parser is None:
                parser = parser_fact
        trees.append(tree)
    return trees

def parse_query(s):
    tokens = lexer.tokenize(s, eof=True)
    s = parser_query.parse(tokens, lazy=False)

def parse_query_term(s):
    return get_query_and_vars(s)[0]

def get_query_and_vars(s):
    tokens = lexer.tokenize(s, eof=True)
    s = parser_query.parse(tokens, lazy=False)
    builder = TermBuilder()
    query = builder.build(s)
    return query, builder.varname_to_var

class OrderTransformer(object):
    def transform(self, node):
        if isinstance(node, Symbol):
            return node
        children = [c for c in node.children
                        if isinstance(c, Symbol) or (
                            isinstance(c, Nonterminal) and len(c.children))]
        if isinstance(node, Nonterminal):
            if len(children) == 1:
                return Nonterminal(
                    node.symbol, [self.transform(children[0])])
            if len(children) == 2 or len(children) == 3:
                left = children[-2]
                right = children[-1]
                if (isinstance(right, Nonterminal) and
                    right.symbol.startswith("extraexpr")):
                    if len(children) == 2:
                        leftreplacement = self.transform(left)
                    else:
                        leftreplacement = Nonterminal(
                            node.symbol,
                            [self.transform(children[0]),
                             self.transform(left)])
                    children = [leftreplacement,
                                self.transform(right.children[0]),
                                self.transform(right.children[1])]

                    newnode = Nonterminal(node.symbol, children)
                    return self.transform_extra(right, newnode)
            children = [self.transform(child) for child in children]
            return Nonterminal(node.symbol, children)

    def transform_extra(self, extranode, child):
        children = [c for c in extranode.children
                        if isinstance(c, Symbol) or (
                            isinstance(c, Nonterminal) and len(c.children))]
        symbol = extranode.symbol[5:]
        if len(children) == 2:
            return child
        right = children[2]
        assert isinstance(right, Nonterminal)
        children = [child,
                    self.transform(right.children[0]),
                    self.transform(right.children[1])]
        newnode = Nonterminal(symbol, children)
        return self.transform_extra(right, newnode)

class TermBuilder(RPythonVisitor):

    def __init__(self):
        self.varname_to_var = {}

    def build(self, s):
        "NOT_RPYTHON"
        if isinstance(s, list):
            return self.build_many(s)
        return self.build_query(s)

    def build_many(self, trees):
        ot = OrderTransformer()
        facts = []
        for tree in trees:
            s = ot.transform(tree)
            facts.append(self.build_fact(s))
        return facts

    def build_query(self, s):
        ot = OrderTransformer()
        s = ot.transform(s)
        return self.visit(s.children[0])

    def build_fact(self, node):
        self.varname_to_var = {}
        return self.visit(node.children[0])

    def visit(self, node):
        node = self.find_first_interesting(node)
        return self.dispatch(node)

    def general_nonterminal_visit(self, node):
        from prolog.interpreter.term import Callable, Number, Float, BigInt
        children = []
        name = ""
        for child in node.children:
            if isinstance(child, Symbol):
                name = self.general_symbol_visit(child).name()            
            else:
                children.append(child)
        children = [self.visit(child) for child in children]
        if len(children) == 1 and (name == "-" or name == "+"):
            if name == "-":
                factor = -1
            else:
                factor = 1
            child = children[0]
            if isinstance(child, Number):
                return Number(factor * child.num)
            if isinstance(child, Float):
                return Float(factor * child.floatval)
            if isinstance(child, BigInt):
                return BigInt(rbigint.fromint(factor).mul(child.value))
        return Callable.build(name, children)

    def build_list(self, node):
        result = []
        while node is not None:
            node = self._build_list(node, result)
        return result

    def _build_list(self, node, result):
        node = self.find_first_interesting(node)
        if isinstance(node, Nonterminal):
            child = node.children[1]
            if (isinstance(child, Symbol) and
                node.children[1].additional_info == ","):
                element = self.visit(node.children[0])
                result.append(element)
                return node.children[2]
        result.append(self.visit(node))

    def find_first_interesting(self, node):
        if isinstance(node, Nonterminal) and len(node.children) == 1:
            return self.find_first_interesting(node.children[0])
        return node

    def general_symbol_visit(self, node):
        from prolog.interpreter.term import Callable
        if node.additional_info.startswith("'"):
            end = len(node.additional_info) - 1
            assert end >= 0
            name = unescape(node.additional_info[1:end])
        else:
            name = node.additional_info
        return Callable.build(name)

    def visit_VAR(self, node):
        from prolog.interpreter.term import Var
        varname = node.additional_info
        if varname == "_":
            return Var()
        if varname in self.varname_to_var:
            return self.varname_to_var[varname]
        res = Var()
        self.varname_to_var[varname] = res
        return res

    def visit_NUMBER(self, node):
        from prolog.interpreter.term import Number, Float, BigInt
        s = node.additional_info
        try:
            try:
                ovfcheck(int(s))
            except OverflowError:
                return BigInt(rbigint.fromdecimalstr(s))
            return Number(int(s))
        except ValueError:
            return Float(float(s))

    def visit_STRING(self, node):
        from prolog.interpreter import helper
        from prolog.interpreter.term import Callable, Number
        info = node.additional_info
        s = unicode(info[1:len(info) - 1], "utf8")
        l = [Number(ord(c)) for c in s]
        return helper.wrap_list(l)

    def visit_complexterm(self, node):
        from prolog.interpreter.term import Callable
        name = self.general_symbol_visit(node.children[0]).name()
        children = self.build_list(node.children[2])
        return Callable.build(name, children[:])

    def visit_expr(self, node):
        from prolog.interpreter.term import Number, Float, BigInt
        additional_info = node.children[0].additional_info
        result = self.visit(node.children[1])
        if additional_info == '-':
            if isinstance(result, Number):
                return Number(-result.num)
            elif isinstance(result, Float):
                return Float(-result.floatval)
        elif additional_info == "{":
            from prolog.interpreter.term import Callable
            return Callable.build("{}", [result])
        return result

    def visit_listexpr(self, node):
        from prolog.interpreter.term import Callable
        node = node.children[1]
        if len(node.children) == 1:
            l = self.build_list(node)
            start = Callable.build("[]")
        else:
            l = self.build_list(node.children[0])
            start = self.visit(node.children[2])
        l.reverse()
        curr = start
        for elt in l:
            curr = Callable.build(".", [elt, curr])
        return curr


ESCAPES = {
    "\\a": "\a",
    "\\b": "\b",
    "\\f": "\f",
    "\\n": "\n",
    "\\r": "\r",
    "\\t": "\t",
    "\\v": "\v",
    "\\\\":  "\\"
}


def unescape(s):
    if "\\" not in s:
        return s
    result = []
    i = 0
    escape = False
    while i < len(s):
        c = s[i]
        if escape:
            escape = False
            f = "\\" + c
            if f in ESCAPES:
                result.append(ESCAPES[f])
            else:
                result.append(c)
        elif c == "\\":
            escape = True
        else:
            result.append(c)
        i += 1
    return "".join(result)

def get_engine(source, create_files=False, load_system=False, **modules):
    from prolog.interpreter.continuation import Engine
    from prolog.interpreter.test.tool import create_file, delete_file
    e = Engine(load_system)
    for name, module in modules.iteritems():
        if create_files:
            create_file(name, module)
        else:
            e.runstring(module)
    try:
        e.current_module = e.user_module
        e.runstring(source)
    finally:
        if create_files:
            for name in modules.keys():
                delete_file(name)
    return e

# generated code between this line and its other occurence

parser_fact = PrologPackratParser([Rule('query', [['toplevel_op_expr', '.', 'EOF']]),
  Rule('fact', [['toplevel_op_expr', '.']]),
  Rule('complexterm', [['ATOM', '(', 'toplevel_op_expr', ')'], ['expr']]),
  Rule('expr', [['VAR'], ['NUMBER'], ['+', 'NUMBER'], ['-', 'NUMBER'], ['ATOM'], ['STRING'], ['(', 'toplevel_op_expr', ')'], ['{', 'toplevel_op_expr', '}'], ['listexpr']]),
  Rule('listexpr', [['[', 'listbody', ']']]),
  Rule('listbody', [['toplevel_op_expr', '|', 'toplevel_op_expr'], ['toplevel_op_expr']]),
  Rule('extratoplevel_op_expr', [[]]),
  Rule('toplevel_op_expr', [['expr1100', '-->', 'expr1100', 'extratoplevel_op_expr'], ['expr1100', ':-', 'expr1100', 'extratoplevel_op_expr'], [':-', 'expr1100', 'extratoplevel_op_expr'], ['?-', 'expr1100', 'extratoplevel_op_expr'], ['expr1100', 'extratoplevel_op_expr']]),
  Rule('extraexpr1100', [[]]),
  Rule('expr1100', [['expr1050', ';', 'expr1100', 'extraexpr1100'], ['expr1050', 'extraexpr1100']]),
  Rule('extraexpr1050', [[]]),
  Rule('expr1050', [['expr1000', '->', 'expr1050', 'extraexpr1050'], ['expr1000', 'extraexpr1050']]),
  Rule('extraexpr1000', [[]]),
  Rule('expr1000', [['expr900', ',', 'expr1000', 'extraexpr1000'], ['expr900', 'extraexpr1000']]),
  Rule('extraexpr900', [[]]),
  Rule('expr900', [['\\+', 'expr900', 'extraexpr900'], ['~', 'expr700', 'extraexpr900'], ['expr700', 'extraexpr900']]),
  Rule('extraexpr700', [[]]),
  Rule('expr700', [['expr600', '<', 'expr600', 'extraexpr700'], ['expr600', '=', 'expr600', 'extraexpr700'], ['expr600', '=..', 'expr600', 'extraexpr700'], ['expr600', '=@=', 'expr600', 'extraexpr700'], ['expr600', '=:=', 'expr600', 'extraexpr700'], ['expr600', '=<', 'expr600', 'extraexpr700'], ['expr600', '==', 'expr600', 'extraexpr700'], ['expr600', '=\\=', 'expr600', 'extraexpr700'], ['expr600', '>', 'expr600', 'extraexpr700'], ['expr600', '>=', 'expr600', 'extraexpr700'], ['expr600', '@<', 'expr600', 'extraexpr700'], ['expr600', '@=<', 'expr600', 'extraexpr700'], ['expr600', '@>', 'expr600', 'extraexpr700'], ['expr600', '@>=', 'expr600', 'extraexpr700'], ['expr600', '\\=', 'expr600', 'extraexpr700'], ['expr600', '\\==', 'expr600', 'extraexpr700'], ['expr600', 'is', 'expr600', 'extraexpr700'], ['expr600', 'extraexpr700']]),
  Rule('extraexpr600', [[]]),
  Rule('expr600', [['expr500', ':', 'expr600', 'extraexpr600'], ['expr500', 'extraexpr600']]),
  Rule('extraexpr500', [['+', 'expr400', 'extraexpr500'], ['-', 'expr400', 'extraexpr500'], ['/\\', 'expr400', 'extraexpr500'], ['\\/', 'expr400', 'extraexpr500'], ['xor', 'expr400', 'extraexpr500'], []]),
  Rule('expr500', [['+', 'expr400', 'extraexpr500'], ['-', 'expr400', 'extraexpr500'], ['?', 'expr400', 'extraexpr500'], ['\\', 'expr400', 'extraexpr500'], ['expr400', 'extraexpr500']]),
  Rule('extraexpr400', [['*', 'expr200', 'extraexpr400'], ['/', 'expr200', 'extraexpr400'], ['//', 'expr200', 'extraexpr400'], ['<<', 'expr200', 'extraexpr400'], ['>>', 'expr200', 'extraexpr400'], ['mod', 'expr200', 'extraexpr400'], ['rem', 'expr200', 'extraexpr400'], []]),
  Rule('expr400', [['expr200', 'extraexpr400']]),
  Rule('extraexpr200', [[]]),
  Rule('expr200', [['complexterm', '**', 'complexterm', 'extraexpr200'], ['complexterm', '^', 'expr200', 'extraexpr200'], ['complexterm', 'extraexpr200']])],
 'fact')
parser_query = PrologPackratParser([Rule('query', [['toplevel_op_expr', '.', 'EOF']]),
  Rule('fact', [['toplevel_op_expr', '.']]),
  Rule('complexterm', [['ATOM', '(', 'toplevel_op_expr', ')'], ['expr']]),
  Rule('expr', [['VAR'], ['NUMBER'], ['+', 'NUMBER'], ['-', 'NUMBER'], ['ATOM'], ['STRING'], ['(', 'toplevel_op_expr', ')'], ['{', 'toplevel_op_expr', '}'], ['listexpr']]),
  Rule('listexpr', [['[', 'listbody', ']']]),
  Rule('listbody', [['toplevel_op_expr', '|', 'toplevel_op_expr'], ['toplevel_op_expr']]),
  Rule('extratoplevel_op_expr', [[]]),
  Rule('toplevel_op_expr', [['expr1100', '-->', 'expr1100', 'extratoplevel_op_expr'], ['expr1100', ':-', 'expr1100', 'extratoplevel_op_expr'], [':-', 'expr1100', 'extratoplevel_op_expr'], ['?-', 'expr1100', 'extratoplevel_op_expr'], ['expr1100', 'extratoplevel_op_expr']]),
  Rule('extraexpr1100', [[]]),
  Rule('expr1100', [['expr1050', ';', 'expr1100', 'extraexpr1100'], ['expr1050', 'extraexpr1100']]),
  Rule('extraexpr1050', [[]]),
  Rule('expr1050', [['expr1000', '->', 'expr1050', 'extraexpr1050'], ['expr1000', 'extraexpr1050']]),
  Rule('extraexpr1000', [[]]),
  Rule('expr1000', [['expr900', ',', 'expr1000', 'extraexpr1000'], ['expr900', 'extraexpr1000']]),
  Rule('extraexpr900', [[]]),
  Rule('expr900', [['\\+', 'expr900', 'extraexpr900'], ['~', 'expr700', 'extraexpr900'], ['expr700', 'extraexpr900']]),
  Rule('extraexpr700', [[]]),
  Rule('expr700', [['expr600', '<', 'expr600', 'extraexpr700'], ['expr600', '=', 'expr600', 'extraexpr700'], ['expr600', '=..', 'expr600', 'extraexpr700'], ['expr600', '=@=', 'expr600', 'extraexpr700'], ['expr600', '=:=', 'expr600', 'extraexpr700'], ['expr600', '=<', 'expr600', 'extraexpr700'], ['expr600', '==', 'expr600', 'extraexpr700'], ['expr600', '=\\=', 'expr600', 'extraexpr700'], ['expr600', '>', 'expr600', 'extraexpr700'], ['expr600', '>=', 'expr600', 'extraexpr700'], ['expr600', '@<', 'expr600', 'extraexpr700'], ['expr600', '@=<', 'expr600', 'extraexpr700'], ['expr600', '@>', 'expr600', 'extraexpr700'], ['expr600', '@>=', 'expr600', 'extraexpr700'], ['expr600', '\\=', 'expr600', 'extraexpr700'], ['expr600', '\\==', 'expr600', 'extraexpr700'], ['expr600', 'is', 'expr600', 'extraexpr700'], ['expr600', 'extraexpr700']]),
  Rule('extraexpr600', [[]]),
  Rule('expr600', [['expr500', ':', 'expr600', 'extraexpr600'], ['expr500', 'extraexpr600']]),
  Rule('extraexpr500', [['+', 'expr400', 'extraexpr500'], ['-', 'expr400', 'extraexpr500'], ['/\\', 'expr400', 'extraexpr500'], ['\\/', 'expr400', 'extraexpr500'], ['xor', 'expr400', 'extraexpr500'], []]),
  Rule('expr500', [['+', 'expr400', 'extraexpr500'], ['-', 'expr400', 'extraexpr500'], ['?', 'expr400', 'extraexpr500'], ['\\', 'expr400', 'extraexpr500'], ['expr400', 'extraexpr500']]),
  Rule('extraexpr400', [['*', 'expr200', 'extraexpr400'], ['/', 'expr200', 'extraexpr400'], ['//', 'expr200', 'extraexpr400'], ['<<', 'expr200', 'extraexpr400'], ['>>', 'expr200', 'extraexpr400'], ['mod', 'expr200', 'extraexpr400'], ['rem', 'expr200', 'extraexpr400'], []]),
  Rule('expr400', [['expr200', 'extraexpr400']]),
  Rule('extraexpr200', [[]]),
  Rule('expr200', [['complexterm', '**', 'complexterm', 'extraexpr200'], ['complexterm', '^', 'expr200', 'extraexpr200'], ['complexterm', 'extraexpr200']])],
 'query')
def recognize(runner, i):
    #auto-generated code, don't edit
    assert i >= 0
    input = runner.text
    state = 0
    while 1:
        if state == 0:
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 0
                return ~i
            if char == '\t':
                state = 1
            elif char == '\n':
                state = 1
            elif char == ' ':
                state = 1
            elif char == '(':
                state = 2
            elif char == ',':
                state = 3
            elif char == '0':
                state = 4
            elif '1' <= char <= '9':
                state = 5
            elif char == '<':
                state = 6
            elif char == '@':
                state = 7
            elif 'A' <= char <= 'Z':
                state = 8
            elif char == '_':
                state = 8
            elif char == '\\':
                state = 9
            elif 'a' <= char <= 'h':
                state = 10
            elif 's' <= char <= 'w':
                state = 10
            elif 'n' <= char <= 'q':
                state = 10
            elif 'j' <= char <= 'l':
                state = 10
            elif char == 'y':
                state = 10
            elif char == 'z':
                state = 10
            elif char == 'x':
                state = 11
            elif char == '|':
                state = 12
            elif char == "'":
                state = 13
            elif char == '+':
                state = 14
            elif char == '/':
                state = 15
            elif char == ';':
                state = 16
            elif char == '?':
                state = 17
            elif char == '[':
                state = 18
            elif char == '{':
                state = 19
            elif char == '"':
                state = 20
            elif char == '*':
                state = 21
            elif char == '.':
                state = 22
            elif char == ':':
                state = 23
            elif char == '>':
                state = 24
            elif char == '^':
                state = 25
            elif char == 'r':
                state = 26
            elif char == '~':
                state = 27
            elif char == '!':
                state = 28
            elif char == '%':
                state = 29
            elif char == ')':
                state = 30
            elif char == '-':
                state = 31
            elif char == '=':
                state = 32
            elif char == ']':
                state = 33
            elif char == 'i':
                state = 34
            elif char == 'm':
                state = 35
            elif char == '}':
                state = 36
            else:
                break
        if state == 4:
            runner.last_matched_index = i - 1
            runner.last_matched_state = state
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 4
                return i
            if char == '.':
                state = 77
            else:
                break
        if state == 5:
            runner.last_matched_index = i - 1
            runner.last_matched_state = state
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 5
                return i
            if '0' <= char <= '9':
                state = 5
                continue
            elif char == '.':
                state = 77
            else:
                break
        if state == 6:
            runner.last_matched_index = i - 1
            runner.last_matched_state = state
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 6
                return i
            if char == '<':
                state = 76
            else:
                break
        if state == 7:
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 7
                return ~i
            if char == '<':
                state = 72
            elif char == '>':
                state = 73
            elif char == '=':
                state = 71
            else:
                break
        if state == 8:
            runner.last_matched_index = i - 1
            runner.last_matched_state = state
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 8
                return i
            if 'A' <= char <= 'Z':
                state = 8
                continue
            elif 'a' <= char <= 'z':
                state = 8
                continue
            elif '0' <= char <= '9':
                state = 8
                continue
            elif char == '_':
                state = 8
                continue
            else:
                break
        if state == 9:
            runner.last_matched_index = i - 1
            runner.last_matched_state = state
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 9
                return i
            if char == '+':
                state = 67
            elif char == '=':
                state = 68
            elif char == '/':
                state = 69
            else:
                break
        if state == 10:
            runner.last_matched_index = i - 1
            runner.last_matched_state = state
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 10
                return i
            if 'A' <= char <= 'Z':
                state = 10
                continue
            elif 'a' <= char <= 'z':
                state = 10
                continue
            elif '0' <= char <= '9':
                state = 10
                continue
            elif char == '_':
                state = 10
                continue
            else:
                break
        if state == 11:
            runner.last_matched_index = i - 1
            runner.last_matched_state = state
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 11
                return i
            if char == 'o':
                state = 65
            elif 'A' <= char <= 'Z':
                state = 10
                continue
            elif 'a' <= char <= 'n':
                state = 10
                continue
            elif 'p' <= char <= 'z':
                state = 10
                continue
            elif '0' <= char <= '9':
                state = 10
                continue
            elif char == '_':
                state = 10
                continue
            else:
                break
        if state == 13:
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 13
                return ~i
            if char == "'":
                state = 28
            elif '(' <= char <= '\xff':
                state = 13
                continue
            elif '\x00' <= char <= '&':
                state = 13
                continue
            else:
                break
        if state == 15:
            runner.last_matched_index = i - 1
            runner.last_matched_state = state
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 15
                return i
            if char == '*':
                state = 61
            elif char == '\\':
                state = 62
            elif char == '/':
                state = 63
            else:
                break
        if state == 17:
            runner.last_matched_index = i - 1
            runner.last_matched_state = state
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 17
                return i
            if char == '-':
                state = 60
            else:
                break
        if state == 18:
            runner.last_matched_index = i - 1
            runner.last_matched_state = state
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 18
                return i
            if char == ']':
                state = 28
            else:
                break
        if state == 19:
            runner.last_matched_index = i - 1
            runner.last_matched_state = state
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 19
                return i
            if char == '}':
                state = 28
            else:
                break
        if state == 20:
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 20
                return ~i
            if char == '"':
                state = 59
            elif '#' <= char <= '\xff':
                state = 20
                continue
            elif '\x00' <= char <= '!':
                state = 20
                continue
            else:
                break
        if state == 21:
            runner.last_matched_index = i - 1
            runner.last_matched_state = state
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 21
                return i
            if char == '*':
                state = 58
            else:
                break
        if state == 23:
            runner.last_matched_index = i - 1
            runner.last_matched_state = state
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 23
                return i
            if char == '-':
                state = 57
            else:
                break
        if state == 24:
            runner.last_matched_index = i - 1
            runner.last_matched_state = state
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 24
                return i
            if char == '>':
                state = 56
            elif char == '=':
                state = 55
            else:
                break
        if state == 26:
            runner.last_matched_index = i - 1
            runner.last_matched_state = state
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 26
                return i
            if 'A' <= char <= 'Z':
                state = 10
                continue
            elif 'f' <= char <= 'z':
                state = 10
                continue
            elif '0' <= char <= '9':
                state = 10
                continue
            elif 'a' <= char <= 'd':
                state = 10
                continue
            elif char == '_':
                state = 10
                continue
            elif char == 'e':
                state = 53
            else:
                break
        if state == 29:
            runner.last_matched_index = i - 1
            runner.last_matched_state = state
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 29
                return i
            if '\x0b' <= char <= '\xff':
                state = 29
                continue
            elif '\x00' <= char <= '\t':
                state = 29
                continue
            else:
                break
        if state == 31:
            runner.last_matched_index = i - 1
            runner.last_matched_state = state
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 31
                return i
            if char == '-':
                state = 50
            elif char == '>':
                state = 51
            else:
                break
        if state == 32:
            runner.last_matched_index = i - 1
            runner.last_matched_state = state
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 32
                return i
            if char == '@':
                state = 40
            elif char == '<':
                state = 41
            elif char == '.':
                state = 42
            elif char == ':':
                state = 43
            elif char == '=':
                state = 44
            elif char == '\\':
                state = 45
            else:
                break
        if state == 34:
            runner.last_matched_index = i - 1
            runner.last_matched_state = state
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 34
                return i
            if 'A' <= char <= 'Z':
                state = 10
                continue
            elif 'a' <= char <= 'r':
                state = 10
                continue
            elif '0' <= char <= '9':
                state = 10
                continue
            elif 't' <= char <= 'z':
                state = 10
                continue
            elif char == '_':
                state = 10
                continue
            elif char == 's':
                state = 39
            else:
                break
        if state == 35:
            runner.last_matched_index = i - 1
            runner.last_matched_state = state
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 35
                return i
            if 'A' <= char <= 'Z':
                state = 10
                continue
            elif 'a' <= char <= 'n':
                state = 10
                continue
            elif 'p' <= char <= 'z':
                state = 10
                continue
            elif '0' <= char <= '9':
                state = 10
                continue
            elif char == '_':
                state = 10
                continue
            elif char == 'o':
                state = 37
            else:
                break
        if state == 37:
            runner.last_matched_index = i - 1
            runner.last_matched_state = state
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 37
                return i
            if 'A' <= char <= 'Z':
                state = 10
                continue
            elif 'e' <= char <= 'z':
                state = 10
                continue
            elif '0' <= char <= '9':
                state = 10
                continue
            elif 'a' <= char <= 'c':
                state = 10
                continue
            elif char == '_':
                state = 10
                continue
            elif char == 'd':
                state = 38
            else:
                break
        if state == 38:
            runner.last_matched_index = i - 1
            runner.last_matched_state = state
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 38
                return i
            if 'A' <= char <= 'Z':
                state = 10
                continue
            elif 'a' <= char <= 'z':
                state = 10
                continue
            elif '0' <= char <= '9':
                state = 10
                continue
            elif char == '_':
                state = 10
                continue
            else:
                break
        if state == 39:
            runner.last_matched_index = i - 1
            runner.last_matched_state = state
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 39
                return i
            if 'A' <= char <= 'Z':
                state = 10
                continue
            elif 'a' <= char <= 'z':
                state = 10
                continue
            elif '0' <= char <= '9':
                state = 10
                continue
            elif char == '_':
                state = 10
                continue
            else:
                break
        if state == 40:
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 40
                return ~i
            if char == '=':
                state = 49
            else:
                break
        if state == 42:
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 42
                return ~i
            if char == '.':
                state = 48
            else:
                break
        if state == 43:
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 43
                return ~i
            if char == '=':
                state = 47
            else:
                break
        if state == 45:
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 45
                return ~i
            if char == '=':
                state = 46
            else:
                break
        if state == 50:
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 50
                return ~i
            if char == '>':
                state = 52
            else:
                break
        if state == 53:
            runner.last_matched_index = i - 1
            runner.last_matched_state = state
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 53
                return i
            if 'A' <= char <= 'Z':
                state = 10
                continue
            elif 'n' <= char <= 'z':
                state = 10
                continue
            elif 'a' <= char <= 'l':
                state = 10
                continue
            elif '0' <= char <= '9':
                state = 10
                continue
            elif char == '_':
                state = 10
                continue
            elif char == 'm':
                state = 54
            else:
                break
        if state == 54:
            runner.last_matched_index = i - 1
            runner.last_matched_state = state
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 54
                return i
            if 'A' <= char <= 'Z':
                state = 10
                continue
            elif 'a' <= char <= 'z':
                state = 10
                continue
            elif '0' <= char <= '9':
                state = 10
                continue
            elif char == '_':
                state = 10
                continue
            else:
                break
        if state == 61:
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 61
                return ~i
            if char == '*':
                state = 64
            elif '+' <= char <= '\xff':
                state = 61
                continue
            elif '\x00' <= char <= ')':
                state = 61
                continue
            else:
                break
        if state == 64:
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 64
                return ~i
            if char == '/':
                state = 1
            elif '0' <= char <= '\xff':
                state = 61
                continue
            elif '\x00' <= char <= '.':
                state = 61
                continue
            else:
                break
        if state == 65:
            runner.last_matched_index = i - 1
            runner.last_matched_state = state
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 65
                return i
            if 'A' <= char <= 'Z':
                state = 10
                continue
            elif 'a' <= char <= 'q':
                state = 10
                continue
            elif '0' <= char <= '9':
                state = 10
                continue
            elif 's' <= char <= 'z':
                state = 10
                continue
            elif char == '_':
                state = 10
                continue
            elif char == 'r':
                state = 66
            else:
                break
        if state == 66:
            runner.last_matched_index = i - 1
            runner.last_matched_state = state
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 66
                return i
            if 'A' <= char <= 'Z':
                state = 10
                continue
            elif 'a' <= char <= 'z':
                state = 10
                continue
            elif '0' <= char <= '9':
                state = 10
                continue
            elif char == '_':
                state = 10
                continue
            else:
                break
        if state == 68:
            runner.last_matched_index = i - 1
            runner.last_matched_state = state
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 68
                return i
            if char == '=':
                state = 70
            else:
                break
        if state == 71:
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 71
                return ~i
            if char == '<':
                state = 75
            else:
                break
        if state == 73:
            runner.last_matched_index = i - 1
            runner.last_matched_state = state
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 73
                return i
            if char == '=':
                state = 74
            else:
                break
        if state == 77:
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 77
                return ~i
            if '0' <= char <= '9':
                state = 78
            else:
                break
        if state == 78:
            runner.last_matched_index = i - 1
            runner.last_matched_state = state
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 78
                return i
            if '0' <= char <= '9':
                state = 78
                continue
            else:
                break
        runner.last_matched_state = state
        runner.last_matched_index = i - 1
        runner.state = state
        if i == len(input):
            return i
        else:
            return ~i
        break
    runner.state = state
    return ~i
lexer = DummyLexer(recognize, DFA(79,
 {(0, '\t'): 1,
  (0, '\n'): 1,
  (0, ' '): 1,
  (0, '!'): 28,
  (0, '"'): 20,
  (0, '%'): 29,
  (0, "'"): 13,
  (0, '('): 2,
  (0, ')'): 30,
  (0, '*'): 21,
  (0, '+'): 14,
  (0, ','): 3,
  (0, '-'): 31,
  (0, '.'): 22,
  (0, '/'): 15,
  (0, '0'): 4,
  (0, '1'): 5,
  (0, '2'): 5,
  (0, '3'): 5,
  (0, '4'): 5,
  (0, '5'): 5,
  (0, '6'): 5,
  (0, '7'): 5,
  (0, '8'): 5,
  (0, '9'): 5,
  (0, ':'): 23,
  (0, ';'): 16,
  (0, '<'): 6,
  (0, '='): 32,
  (0, '>'): 24,
  (0, '?'): 17,
  (0, '@'): 7,
  (0, 'A'): 8,
  (0, 'B'): 8,
  (0, 'C'): 8,
  (0, 'D'): 8,
  (0, 'E'): 8,
  (0, 'F'): 8,
  (0, 'G'): 8,
  (0, 'H'): 8,
  (0, 'I'): 8,
  (0, 'J'): 8,
  (0, 'K'): 8,
  (0, 'L'): 8,
  (0, 'M'): 8,
  (0, 'N'): 8,
  (0, 'O'): 8,
  (0, 'P'): 8,
  (0, 'Q'): 8,
  (0, 'R'): 8,
  (0, 'S'): 8,
  (0, 'T'): 8,
  (0, 'U'): 8,
  (0, 'V'): 8,
  (0, 'W'): 8,
  (0, 'X'): 8,
  (0, 'Y'): 8,
  (0, 'Z'): 8,
  (0, '['): 18,
  (0, '\\'): 9,
  (0, ']'): 33,
  (0, '^'): 25,
  (0, '_'): 8,
  (0, 'a'): 10,
  (0, 'b'): 10,
  (0, 'c'): 10,
  (0, 'd'): 10,
  (0, 'e'): 10,
  (0, 'f'): 10,
  (0, 'g'): 10,
  (0, 'h'): 10,
  (0, 'i'): 34,
  (0, 'j'): 10,
  (0, 'k'): 10,
  (0, 'l'): 10,
  (0, 'm'): 35,
  (0, 'n'): 10,
  (0, 'o'): 10,
  (0, 'p'): 10,
  (0, 'q'): 10,
  (0, 'r'): 26,
  (0, 's'): 10,
  (0, 't'): 10,
  (0, 'u'): 10,
  (0, 'v'): 10,
  (0, 'w'): 10,
  (0, 'x'): 11,
  (0, 'y'): 10,
  (0, 'z'): 10,
  (0, '{'): 19,
  (0, '|'): 12,
  (0, '}'): 36,
  (0, '~'): 27,
  (4, '.'): 77,
  (5, '.'): 77,
  (5, '0'): 5,
  (5, '1'): 5,
  (5, '2'): 5,
  (5, '3'): 5,
  (5, '4'): 5,
  (5, '5'): 5,
  (5, '6'): 5,
  (5, '7'): 5,
  (5, '8'): 5,
  (5, '9'): 5,
  (6, '<'): 76,
  (7, '<'): 72,
  (7, '='): 71,
  (7, '>'): 73,
  (8, '0'): 8,
  (8, '1'): 8,
  (8, '2'): 8,
  (8, '3'): 8,
  (8, '4'): 8,
  (8, '5'): 8,
  (8, '6'): 8,
  (8, '7'): 8,
  (8, '8'): 8,
  (8, '9'): 8,
  (8, 'A'): 8,
  (8, 'B'): 8,
  (8, 'C'): 8,
  (8, 'D'): 8,
  (8, 'E'): 8,
  (8, 'F'): 8,
  (8, 'G'): 8,
  (8, 'H'): 8,
  (8, 'I'): 8,
  (8, 'J'): 8,
  (8, 'K'): 8,
  (8, 'L'): 8,
  (8, 'M'): 8,
  (8, 'N'): 8,
  (8, 'O'): 8,
  (8, 'P'): 8,
  (8, 'Q'): 8,
  (8, 'R'): 8,
  (8, 'S'): 8,
  (8, 'T'): 8,
  (8, 'U'): 8,
  (8, 'V'): 8,
  (8, 'W'): 8,
  (8, 'X'): 8,
  (8, 'Y'): 8,
  (8, 'Z'): 8,
  (8, '_'): 8,
  (8, 'a'): 8,
  (8, 'b'): 8,
  (8, 'c'): 8,
  (8, 'd'): 8,
  (8, 'e'): 8,
  (8, 'f'): 8,
  (8, 'g'): 8,
  (8, 'h'): 8,
  (8, 'i'): 8,
  (8, 'j'): 8,
  (8, 'k'): 8,
  (8, 'l'): 8,
  (8, 'm'): 8,
  (8, 'n'): 8,
  (8, 'o'): 8,
  (8, 'p'): 8,
  (8, 'q'): 8,
  (8, 'r'): 8,
  (8, 's'): 8,
  (8, 't'): 8,
  (8, 'u'): 8,
  (8, 'v'): 8,
  (8, 'w'): 8,
  (8, 'x'): 8,
  (8, 'y'): 8,
  (8, 'z'): 8,
  (9, '+'): 67,
  (9, '/'): 69,
  (9, '='): 68,
  (10, '0'): 10,
  (10, '1'): 10,
  (10, '2'): 10,
  (10, '3'): 10,
  (10, '4'): 10,
  (10, '5'): 10,
  (10, '6'): 10,
  (10, '7'): 10,
  (10, '8'): 10,
  (10, '9'): 10,
  (10, 'A'): 10,
  (10, 'B'): 10,
  (10, 'C'): 10,
  (10, 'D'): 10,
  (10, 'E'): 10,
  (10, 'F'): 10,
  (10, 'G'): 10,
  (10, 'H'): 10,
  (10, 'I'): 10,
  (10, 'J'): 10,
  (10, 'K'): 10,
  (10, 'L'): 10,
  (10, 'M'): 10,
  (10, 'N'): 10,
  (10, 'O'): 10,
  (10, 'P'): 10,
  (10, 'Q'): 10,
  (10, 'R'): 10,
  (10, 'S'): 10,
  (10, 'T'): 10,
  (10, 'U'): 10,
  (10, 'V'): 10,
  (10, 'W'): 10,
  (10, 'X'): 10,
  (10, 'Y'): 10,
  (10, 'Z'): 10,
  (10, '_'): 10,
  (10, 'a'): 10,
  (10, 'b'): 10,
  (10, 'c'): 10,
  (10, 'd'): 10,
  (10, 'e'): 10,
  (10, 'f'): 10,
  (10, 'g'): 10,
  (10, 'h'): 10,
  (10, 'i'): 10,
  (10, 'j'): 10,
  (10, 'k'): 10,
  (10, 'l'): 10,
  (10, 'm'): 10,
  (10, 'n'): 10,
  (10, 'o'): 10,
  (10, 'p'): 10,
  (10, 'q'): 10,
  (10, 'r'): 10,
  (10, 's'): 10,
  (10, 't'): 10,
  (10, 'u'): 10,
  (10, 'v'): 10,
  (10, 'w'): 10,
  (10, 'x'): 10,
  (10, 'y'): 10,
  (10, 'z'): 10,
  (11, '0'): 10,
  (11, '1'): 10,
  (11, '2'): 10,
  (11, '3'): 10,
  (11, '4'): 10,
  (11, '5'): 10,
  (11, '6'): 10,
  (11, '7'): 10,
  (11, '8'): 10,
  (11, '9'): 10,
  (11, 'A'): 10,
  (11, 'B'): 10,
  (11, 'C'): 10,
  (11, 'D'): 10,
  (11, 'E'): 10,
  (11, 'F'): 10,
  (11, 'G'): 10,
  (11, 'H'): 10,
  (11, 'I'): 10,
  (11, 'J'): 10,
  (11, 'K'): 10,
  (11, 'L'): 10,
  (11, 'M'): 10,
  (11, 'N'): 10,
  (11, 'O'): 10,
  (11, 'P'): 10,
  (11, 'Q'): 10,
  (11, 'R'): 10,
  (11, 'S'): 10,
  (11, 'T'): 10,
  (11, 'U'): 10,
  (11, 'V'): 10,
  (11, 'W'): 10,
  (11, 'X'): 10,
  (11, 'Y'): 10,
  (11, 'Z'): 10,
  (11, '_'): 10,
  (11, 'a'): 10,
  (11, 'b'): 10,
  (11, 'c'): 10,
  (11, 'd'): 10,
  (11, 'e'): 10,
  (11, 'f'): 10,
  (11, 'g'): 10,
  (11, 'h'): 10,
  (11, 'i'): 10,
  (11, 'j'): 10,
  (11, 'k'): 10,
  (11, 'l'): 10,
  (11, 'm'): 10,
  (11, 'n'): 10,
  (11, 'o'): 65,
  (11, 'p'): 10,
  (11, 'q'): 10,
  (11, 'r'): 10,
  (11, 's'): 10,
  (11, 't'): 10,
  (11, 'u'): 10,
  (11, 'v'): 10,
  (11, 'w'): 10,
  (11, 'x'): 10,
  (11, 'y'): 10,
  (11, 'z'): 10,
  (13, '\x00'): 13,
  (13, '\x01'): 13,
  (13, '\x02'): 13,
  (13, '\x03'): 13,
  (13, '\x04'): 13,
  (13, '\x05'): 13,
  (13, '\x06'): 13,
  (13, '\x07'): 13,
  (13, '\x08'): 13,
  (13, '\t'): 13,
  (13, '\n'): 13,
  (13, '\x0b'): 13,
  (13, '\x0c'): 13,
  (13, '\r'): 13,
  (13, '\x0e'): 13,
  (13, '\x0f'): 13,
  (13, '\x10'): 13,
  (13, '\x11'): 13,
  (13, '\x12'): 13,
  (13, '\x13'): 13,
  (13, '\x14'): 13,
  (13, '\x15'): 13,
  (13, '\x16'): 13,
  (13, '\x17'): 13,
  (13, '\x18'): 13,
  (13, '\x19'): 13,
  (13, '\x1a'): 13,
  (13, '\x1b'): 13,
  (13, '\x1c'): 13,
  (13, '\x1d'): 13,
  (13, '\x1e'): 13,
  (13, '\x1f'): 13,
  (13, ' '): 13,
  (13, '!'): 13,
  (13, '"'): 13,
  (13, '#'): 13,
  (13, '$'): 13,
  (13, '%'): 13,
  (13, '&'): 13,
  (13, "'"): 28,
  (13, '('): 13,
  (13, ')'): 13,
  (13, '*'): 13,
  (13, '+'): 13,
  (13, ','): 13,
  (13, '-'): 13,
  (13, '.'): 13,
  (13, '/'): 13,
  (13, '0'): 13,
  (13, '1'): 13,
  (13, '2'): 13,
  (13, '3'): 13,
  (13, '4'): 13,
  (13, '5'): 13,
  (13, '6'): 13,
  (13, '7'): 13,
  (13, '8'): 13,
  (13, '9'): 13,
  (13, ':'): 13,
  (13, ';'): 13,
  (13, '<'): 13,
  (13, '='): 13,
  (13, '>'): 13,
  (13, '?'): 13,
  (13, '@'): 13,
  (13, 'A'): 13,
  (13, 'B'): 13,
  (13, 'C'): 13,
  (13, 'D'): 13,
  (13, 'E'): 13,
  (13, 'F'): 13,
  (13, 'G'): 13,
  (13, 'H'): 13,
  (13, 'I'): 13,
  (13, 'J'): 13,
  (13, 'K'): 13,
  (13, 'L'): 13,
  (13, 'M'): 13,
  (13, 'N'): 13,
  (13, 'O'): 13,
  (13, 'P'): 13,
  (13, 'Q'): 13,
  (13, 'R'): 13,
  (13, 'S'): 13,
  (13, 'T'): 13,
  (13, 'U'): 13,
  (13, 'V'): 13,
  (13, 'W'): 13,
  (13, 'X'): 13,
  (13, 'Y'): 13,
  (13, 'Z'): 13,
  (13, '['): 13,
  (13, '\\'): 13,
  (13, ']'): 13,
  (13, '^'): 13,
  (13, '_'): 13,
  (13, '`'): 13,
  (13, 'a'): 13,
  (13, 'b'): 13,
  (13, 'c'): 13,
  (13, 'd'): 13,
  (13, 'e'): 13,
  (13, 'f'): 13,
  (13, 'g'): 13,
  (13, 'h'): 13,
  (13, 'i'): 13,
  (13, 'j'): 13,
  (13, 'k'): 13,
  (13, 'l'): 13,
  (13, 'm'): 13,
  (13, 'n'): 13,
  (13, 'o'): 13,
  (13, 'p'): 13,
  (13, 'q'): 13,
  (13, 'r'): 13,
  (13, 's'): 13,
  (13, 't'): 13,
  (13, 'u'): 13,
  (13, 'v'): 13,
  (13, 'w'): 13,
  (13, 'x'): 13,
  (13, 'y'): 13,
  (13, 'z'): 13,
  (13, '{'): 13,
  (13, '|'): 13,
  (13, '}'): 13,
  (13, '~'): 13,
  (13, '\x7f'): 13,
  (13, '\x80'): 13,
  (13, '\x81'): 13,
  (13, '\x82'): 13,
  (13, '\x83'): 13,
  (13, '\x84'): 13,
  (13, '\x85'): 13,
  (13, '\x86'): 13,
  (13, '\x87'): 13,
  (13, '\x88'): 13,
  (13, '\x89'): 13,
  (13, '\x8a'): 13,
  (13, '\x8b'): 13,
  (13, '\x8c'): 13,
  (13, '\x8d'): 13,
  (13, '\x8e'): 13,
  (13, '\x8f'): 13,
  (13, '\x90'): 13,
  (13, '\x91'): 13,
  (13, '\x92'): 13,
  (13, '\x93'): 13,
  (13, '\x94'): 13,
  (13, '\x95'): 13,
  (13, '\x96'): 13,
  (13, '\x97'): 13,
  (13, '\x98'): 13,
  (13, '\x99'): 13,
  (13, '\x9a'): 13,
  (13, '\x9b'): 13,
  (13, '\x9c'): 13,
  (13, '\x9d'): 13,
  (13, '\x9e'): 13,
  (13, '\x9f'): 13,
  (13, '\xa0'): 13,
  (13, '\xa1'): 13,
  (13, '\xa2'): 13,
  (13, '\xa3'): 13,
  (13, '\xa4'): 13,
  (13, '\xa5'): 13,
  (13, '\xa6'): 13,
  (13, '\xa7'): 13,
  (13, '\xa8'): 13,
  (13, '\xa9'): 13,
  (13, '\xaa'): 13,
  (13, '\xab'): 13,
  (13, '\xac'): 13,
  (13, '\xad'): 13,
  (13, '\xae'): 13,
  (13, '\xaf'): 13,
  (13, '\xb0'): 13,
  (13, '\xb1'): 13,
  (13, '\xb2'): 13,
  (13, '\xb3'): 13,
  (13, '\xb4'): 13,
  (13, '\xb5'): 13,
  (13, '\xb6'): 13,
  (13, '\xb7'): 13,
  (13, '\xb8'): 13,
  (13, '\xb9'): 13,
  (13, '\xba'): 13,
  (13, '\xbb'): 13,
  (13, '\xbc'): 13,
  (13, '\xbd'): 13,
  (13, '\xbe'): 13,
  (13, '\xbf'): 13,
  (13, '\xc0'): 13,
  (13, '\xc1'): 13,
  (13, '\xc2'): 13,
  (13, '\xc3'): 13,
  (13, '\xc4'): 13,
  (13, '\xc5'): 13,
  (13, '\xc6'): 13,
  (13, '\xc7'): 13,
  (13, '\xc8'): 13,
  (13, '\xc9'): 13,
  (13, '\xca'): 13,
  (13, '\xcb'): 13,
  (13, '\xcc'): 13,
  (13, '\xcd'): 13,
  (13, '\xce'): 13,
  (13, '\xcf'): 13,
  (13, '\xd0'): 13,
  (13, '\xd1'): 13,
  (13, '\xd2'): 13,
  (13, '\xd3'): 13,
  (13, '\xd4'): 13,
  (13, '\xd5'): 13,
  (13, '\xd6'): 13,
  (13, '\xd7'): 13,
  (13, '\xd8'): 13,
  (13, '\xd9'): 13,
  (13, '\xda'): 13,
  (13, '\xdb'): 13,
  (13, '\xdc'): 13,
  (13, '\xdd'): 13,
  (13, '\xde'): 13,
  (13, '\xdf'): 13,
  (13, '\xe0'): 13,
  (13, '\xe1'): 13,
  (13, '\xe2'): 13,
  (13, '\xe3'): 13,
  (13, '\xe4'): 13,
  (13, '\xe5'): 13,
  (13, '\xe6'): 13,
  (13, '\xe7'): 13,
  (13, '\xe8'): 13,
  (13, '\xe9'): 13,
  (13, '\xea'): 13,
  (13, '\xeb'): 13,
  (13, '\xec'): 13,
  (13, '\xed'): 13,
  (13, '\xee'): 13,
  (13, '\xef'): 13,
  (13, '\xf0'): 13,
  (13, '\xf1'): 13,
  (13, '\xf2'): 13,
  (13, '\xf3'): 13,
  (13, '\xf4'): 13,
  (13, '\xf5'): 13,
  (13, '\xf6'): 13,
  (13, '\xf7'): 13,
  (13, '\xf8'): 13,
  (13, '\xf9'): 13,
  (13, '\xfa'): 13,
  (13, '\xfb'): 13,
  (13, '\xfc'): 13,
  (13, '\xfd'): 13,
  (13, '\xfe'): 13,
  (13, '\xff'): 13,
  (15, '*'): 61,
  (15, '/'): 63,
  (15, '\\'): 62,
  (17, '-'): 60,
  (18, ']'): 28,
  (19, '}'): 28,
  (20, '\x00'): 20,
  (20, '\x01'): 20,
  (20, '\x02'): 20,
  (20, '\x03'): 20,
  (20, '\x04'): 20,
  (20, '\x05'): 20,
  (20, '\x06'): 20,
  (20, '\x07'): 20,
  (20, '\x08'): 20,
  (20, '\t'): 20,
  (20, '\n'): 20,
  (20, '\x0b'): 20,
  (20, '\x0c'): 20,
  (20, '\r'): 20,
  (20, '\x0e'): 20,
  (20, '\x0f'): 20,
  (20, '\x10'): 20,
  (20, '\x11'): 20,
  (20, '\x12'): 20,
  (20, '\x13'): 20,
  (20, '\x14'): 20,
  (20, '\x15'): 20,
  (20, '\x16'): 20,
  (20, '\x17'): 20,
  (20, '\x18'): 20,
  (20, '\x19'): 20,
  (20, '\x1a'): 20,
  (20, '\x1b'): 20,
  (20, '\x1c'): 20,
  (20, '\x1d'): 20,
  (20, '\x1e'): 20,
  (20, '\x1f'): 20,
  (20, ' '): 20,
  (20, '!'): 20,
  (20, '"'): 59,
  (20, '#'): 20,
  (20, '$'): 20,
  (20, '%'): 20,
  (20, '&'): 20,
  (20, "'"): 20,
  (20, '('): 20,
  (20, ')'): 20,
  (20, '*'): 20,
  (20, '+'): 20,
  (20, ','): 20,
  (20, '-'): 20,
  (20, '.'): 20,
  (20, '/'): 20,
  (20, '0'): 20,
  (20, '1'): 20,
  (20, '2'): 20,
  (20, '3'): 20,
  (20, '4'): 20,
  (20, '5'): 20,
  (20, '6'): 20,
  (20, '7'): 20,
  (20, '8'): 20,
  (20, '9'): 20,
  (20, ':'): 20,
  (20, ';'): 20,
  (20, '<'): 20,
  (20, '='): 20,
  (20, '>'): 20,
  (20, '?'): 20,
  (20, '@'): 20,
  (20, 'A'): 20,
  (20, 'B'): 20,
  (20, 'C'): 20,
  (20, 'D'): 20,
  (20, 'E'): 20,
  (20, 'F'): 20,
  (20, 'G'): 20,
  (20, 'H'): 20,
  (20, 'I'): 20,
  (20, 'J'): 20,
  (20, 'K'): 20,
  (20, 'L'): 20,
  (20, 'M'): 20,
  (20, 'N'): 20,
  (20, 'O'): 20,
  (20, 'P'): 20,
  (20, 'Q'): 20,
  (20, 'R'): 20,
  (20, 'S'): 20,
  (20, 'T'): 20,
  (20, 'U'): 20,
  (20, 'V'): 20,
  (20, 'W'): 20,
  (20, 'X'): 20,
  (20, 'Y'): 20,
  (20, 'Z'): 20,
  (20, '['): 20,
  (20, '\\'): 20,
  (20, ']'): 20,
  (20, '^'): 20,
  (20, '_'): 20,
  (20, '`'): 20,
  (20, 'a'): 20,
  (20, 'b'): 20,
  (20, 'c'): 20,
  (20, 'd'): 20,
  (20, 'e'): 20,
  (20, 'f'): 20,
  (20, 'g'): 20,
  (20, 'h'): 20,
  (20, 'i'): 20,
  (20, 'j'): 20,
  (20, 'k'): 20,
  (20, 'l'): 20,
  (20, 'm'): 20,
  (20, 'n'): 20,
  (20, 'o'): 20,
  (20, 'p'): 20,
  (20, 'q'): 20,
  (20, 'r'): 20,
  (20, 's'): 20,
  (20, 't'): 20,
  (20, 'u'): 20,
  (20, 'v'): 20,
  (20, 'w'): 20,
  (20, 'x'): 20,
  (20, 'y'): 20,
  (20, 'z'): 20,
  (20, '{'): 20,
  (20, '|'): 20,
  (20, '}'): 20,
  (20, '~'): 20,
  (20, '\x7f'): 20,
  (20, '\x80'): 20,
  (20, '\x81'): 20,
  (20, '\x82'): 20,
  (20, '\x83'): 20,
  (20, '\x84'): 20,
  (20, '\x85'): 20,
  (20, '\x86'): 20,
  (20, '\x87'): 20,
  (20, '\x88'): 20,
  (20, '\x89'): 20,
  (20, '\x8a'): 20,
  (20, '\x8b'): 20,
  (20, '\x8c'): 20,
  (20, '\x8d'): 20,
  (20, '\x8e'): 20,
  (20, '\x8f'): 20,
  (20, '\x90'): 20,
  (20, '\x91'): 20,
  (20, '\x92'): 20,
  (20, '\x93'): 20,
  (20, '\x94'): 20,
  (20, '\x95'): 20,
  (20, '\x96'): 20,
  (20, '\x97'): 20,
  (20, '\x98'): 20,
  (20, '\x99'): 20,
  (20, '\x9a'): 20,
  (20, '\x9b'): 20,
  (20, '\x9c'): 20,
  (20, '\x9d'): 20,
  (20, '\x9e'): 20,
  (20, '\x9f'): 20,
  (20, '\xa0'): 20,
  (20, '\xa1'): 20,
  (20, '\xa2'): 20,
  (20, '\xa3'): 20,
  (20, '\xa4'): 20,
  (20, '\xa5'): 20,
  (20, '\xa6'): 20,
  (20, '\xa7'): 20,
  (20, '\xa8'): 20,
  (20, '\xa9'): 20,
  (20, '\xaa'): 20,
  (20, '\xab'): 20,
  (20, '\xac'): 20,
  (20, '\xad'): 20,
  (20, '\xae'): 20,
  (20, '\xaf'): 20,
  (20, '\xb0'): 20,
  (20, '\xb1'): 20,
  (20, '\xb2'): 20,
  (20, '\xb3'): 20,
  (20, '\xb4'): 20,
  (20, '\xb5'): 20,
  (20, '\xb6'): 20,
  (20, '\xb7'): 20,
  (20, '\xb8'): 20,
  (20, '\xb9'): 20,
  (20, '\xba'): 20,
  (20, '\xbb'): 20,
  (20, '\xbc'): 20,
  (20, '\xbd'): 20,
  (20, '\xbe'): 20,
  (20, '\xbf'): 20,
  (20, '\xc0'): 20,
  (20, '\xc1'): 20,
  (20, '\xc2'): 20,
  (20, '\xc3'): 20,
  (20, '\xc4'): 20,
  (20, '\xc5'): 20,
  (20, '\xc6'): 20,
  (20, '\xc7'): 20,
  (20, '\xc8'): 20,
  (20, '\xc9'): 20,
  (20, '\xca'): 20,
  (20, '\xcb'): 20,
  (20, '\xcc'): 20,
  (20, '\xcd'): 20,
  (20, '\xce'): 20,
  (20, '\xcf'): 20,
  (20, '\xd0'): 20,
  (20, '\xd1'): 20,
  (20, '\xd2'): 20,
  (20, '\xd3'): 20,
  (20, '\xd4'): 20,
  (20, '\xd5'): 20,
  (20, '\xd6'): 20,
  (20, '\xd7'): 20,
  (20, '\xd8'): 20,
  (20, '\xd9'): 20,
  (20, '\xda'): 20,
  (20, '\xdb'): 20,
  (20, '\xdc'): 20,
  (20, '\xdd'): 20,
  (20, '\xde'): 20,
  (20, '\xdf'): 20,
  (20, '\xe0'): 20,
  (20, '\xe1'): 20,
  (20, '\xe2'): 20,
  (20, '\xe3'): 20,
  (20, '\xe4'): 20,
  (20, '\xe5'): 20,
  (20, '\xe6'): 20,
  (20, '\xe7'): 20,
  (20, '\xe8'): 20,
  (20, '\xe9'): 20,
  (20, '\xea'): 20,
  (20, '\xeb'): 20,
  (20, '\xec'): 20,
  (20, '\xed'): 20,
  (20, '\xee'): 20,
  (20, '\xef'): 20,
  (20, '\xf0'): 20,
  (20, '\xf1'): 20,
  (20, '\xf2'): 20,
  (20, '\xf3'): 20,
  (20, '\xf4'): 20,
  (20, '\xf5'): 20,
  (20, '\xf6'): 20,
  (20, '\xf7'): 20,
  (20, '\xf8'): 20,
  (20, '\xf9'): 20,
  (20, '\xfa'): 20,
  (20, '\xfb'): 20,
  (20, '\xfc'): 20,
  (20, '\xfd'): 20,
  (20, '\xfe'): 20,
  (20, '\xff'): 20,
  (21, '*'): 58,
  (23, '-'): 57,
  (24, '='): 55,
  (24, '>'): 56,
  (26, '0'): 10,
  (26, '1'): 10,
  (26, '2'): 10,
  (26, '3'): 10,
  (26, '4'): 10,
  (26, '5'): 10,
  (26, '6'): 10,
  (26, '7'): 10,
  (26, '8'): 10,
  (26, '9'): 10,
  (26, 'A'): 10,
  (26, 'B'): 10,
  (26, 'C'): 10,
  (26, 'D'): 10,
  (26, 'E'): 10,
  (26, 'F'): 10,
  (26, 'G'): 10,
  (26, 'H'): 10,
  (26, 'I'): 10,
  (26, 'J'): 10,
  (26, 'K'): 10,
  (26, 'L'): 10,
  (26, 'M'): 10,
  (26, 'N'): 10,
  (26, 'O'): 10,
  (26, 'P'): 10,
  (26, 'Q'): 10,
  (26, 'R'): 10,
  (26, 'S'): 10,
  (26, 'T'): 10,
  (26, 'U'): 10,
  (26, 'V'): 10,
  (26, 'W'): 10,
  (26, 'X'): 10,
  (26, 'Y'): 10,
  (26, 'Z'): 10,
  (26, '_'): 10,
  (26, 'a'): 10,
  (26, 'b'): 10,
  (26, 'c'): 10,
  (26, 'd'): 10,
  (26, 'e'): 53,
  (26, 'f'): 10,
  (26, 'g'): 10,
  (26, 'h'): 10,
  (26, 'i'): 10,
  (26, 'j'): 10,
  (26, 'k'): 10,
  (26, 'l'): 10,
  (26, 'm'): 10,
  (26, 'n'): 10,
  (26, 'o'): 10,
  (26, 'p'): 10,
  (26, 'q'): 10,
  (26, 'r'): 10,
  (26, 's'): 10,
  (26, 't'): 10,
  (26, 'u'): 10,
  (26, 'v'): 10,
  (26, 'w'): 10,
  (26, 'x'): 10,
  (26, 'y'): 10,
  (26, 'z'): 10,
  (29, '\x00'): 29,
  (29, '\x01'): 29,
  (29, '\x02'): 29,
  (29, '\x03'): 29,
  (29, '\x04'): 29,
  (29, '\x05'): 29,
  (29, '\x06'): 29,
  (29, '\x07'): 29,
  (29, '\x08'): 29,
  (29, '\t'): 29,
  (29, '\x0b'): 29,
  (29, '\x0c'): 29,
  (29, '\r'): 29,
  (29, '\x0e'): 29,
  (29, '\x0f'): 29,
  (29, '\x10'): 29,
  (29, '\x11'): 29,
  (29, '\x12'): 29,
  (29, '\x13'): 29,
  (29, '\x14'): 29,
  (29, '\x15'): 29,
  (29, '\x16'): 29,
  (29, '\x17'): 29,
  (29, '\x18'): 29,
  (29, '\x19'): 29,
  (29, '\x1a'): 29,
  (29, '\x1b'): 29,
  (29, '\x1c'): 29,
  (29, '\x1d'): 29,
  (29, '\x1e'): 29,
  (29, '\x1f'): 29,
  (29, ' '): 29,
  (29, '!'): 29,
  (29, '"'): 29,
  (29, '#'): 29,
  (29, '$'): 29,
  (29, '%'): 29,
  (29, '&'): 29,
  (29, "'"): 29,
  (29, '('): 29,
  (29, ')'): 29,
  (29, '*'): 29,
  (29, '+'): 29,
  (29, ','): 29,
  (29, '-'): 29,
  (29, '.'): 29,
  (29, '/'): 29,
  (29, '0'): 29,
  (29, '1'): 29,
  (29, '2'): 29,
  (29, '3'): 29,
  (29, '4'): 29,
  (29, '5'): 29,
  (29, '6'): 29,
  (29, '7'): 29,
  (29, '8'): 29,
  (29, '9'): 29,
  (29, ':'): 29,
  (29, ';'): 29,
  (29, '<'): 29,
  (29, '='): 29,
  (29, '>'): 29,
  (29, '?'): 29,
  (29, '@'): 29,
  (29, 'A'): 29,
  (29, 'B'): 29,
  (29, 'C'): 29,
  (29, 'D'): 29,
  (29, 'E'): 29,
  (29, 'F'): 29,
  (29, 'G'): 29,
  (29, 'H'): 29,
  (29, 'I'): 29,
  (29, 'J'): 29,
  (29, 'K'): 29,
  (29, 'L'): 29,
  (29, 'M'): 29,
  (29, 'N'): 29,
  (29, 'O'): 29,
  (29, 'P'): 29,
  (29, 'Q'): 29,
  (29, 'R'): 29,
  (29, 'S'): 29,
  (29, 'T'): 29,
  (29, 'U'): 29,
  (29, 'V'): 29,
  (29, 'W'): 29,
  (29, 'X'): 29,
  (29, 'Y'): 29,
  (29, 'Z'): 29,
  (29, '['): 29,
  (29, '\\'): 29,
  (29, ']'): 29,
  (29, '^'): 29,
  (29, '_'): 29,
  (29, '`'): 29,
  (29, 'a'): 29,
  (29, 'b'): 29,
  (29, 'c'): 29,
  (29, 'd'): 29,
  (29, 'e'): 29,
  (29, 'f'): 29,
  (29, 'g'): 29,
  (29, 'h'): 29,
  (29, 'i'): 29,
  (29, 'j'): 29,
  (29, 'k'): 29,
  (29, 'l'): 29,
  (29, 'm'): 29,
  (29, 'n'): 29,
  (29, 'o'): 29,
  (29, 'p'): 29,
  (29, 'q'): 29,
  (29, 'r'): 29,
  (29, 's'): 29,
  (29, 't'): 29,
  (29, 'u'): 29,
  (29, 'v'): 29,
  (29, 'w'): 29,
  (29, 'x'): 29,
  (29, 'y'): 29,
  (29, 'z'): 29,
  (29, '{'): 29,
  (29, '|'): 29,
  (29, '}'): 29,
  (29, '~'): 29,
  (29, '\x7f'): 29,
  (29, '\x80'): 29,
  (29, '\x81'): 29,
  (29, '\x82'): 29,
  (29, '\x83'): 29,
  (29, '\x84'): 29,
  (29, '\x85'): 29,
  (29, '\x86'): 29,
  (29, '\x87'): 29,
  (29, '\x88'): 29,
  (29, '\x89'): 29,
  (29, '\x8a'): 29,
  (29, '\x8b'): 29,
  (29, '\x8c'): 29,
  (29, '\x8d'): 29,
  (29, '\x8e'): 29,
  (29, '\x8f'): 29,
  (29, '\x90'): 29,
  (29, '\x91'): 29,
  (29, '\x92'): 29,
  (29, '\x93'): 29,
  (29, '\x94'): 29,
  (29, '\x95'): 29,
  (29, '\x96'): 29,
  (29, '\x97'): 29,
  (29, '\x98'): 29,
  (29, '\x99'): 29,
  (29, '\x9a'): 29,
  (29, '\x9b'): 29,
  (29, '\x9c'): 29,
  (29, '\x9d'): 29,
  (29, '\x9e'): 29,
  (29, '\x9f'): 29,
  (29, '\xa0'): 29,
  (29, '\xa1'): 29,
  (29, '\xa2'): 29,
  (29, '\xa3'): 29,
  (29, '\xa4'): 29,
  (29, '\xa5'): 29,
  (29, '\xa6'): 29,
  (29, '\xa7'): 29,
  (29, '\xa8'): 29,
  (29, '\xa9'): 29,
  (29, '\xaa'): 29,
  (29, '\xab'): 29,
  (29, '\xac'): 29,
  (29, '\xad'): 29,
  (29, '\xae'): 29,
  (29, '\xaf'): 29,
  (29, '\xb0'): 29,
  (29, '\xb1'): 29,
  (29, '\xb2'): 29,
  (29, '\xb3'): 29,
  (29, '\xb4'): 29,
  (29, '\xb5'): 29,
  (29, '\xb6'): 29,
  (29, '\xb7'): 29,
  (29, '\xb8'): 29,
  (29, '\xb9'): 29,
  (29, '\xba'): 29,
  (29, '\xbb'): 29,
  (29, '\xbc'): 29,
  (29, '\xbd'): 29,
  (29, '\xbe'): 29,
  (29, '\xbf'): 29,
  (29, '\xc0'): 29,
  (29, '\xc1'): 29,
  (29, '\xc2'): 29,
  (29, '\xc3'): 29,
  (29, '\xc4'): 29,
  (29, '\xc5'): 29,
  (29, '\xc6'): 29,
  (29, '\xc7'): 29,
  (29, '\xc8'): 29,
  (29, '\xc9'): 29,
  (29, '\xca'): 29,
  (29, '\xcb'): 29,
  (29, '\xcc'): 29,
  (29, '\xcd'): 29,
  (29, '\xce'): 29,
  (29, '\xcf'): 29,
  (29, '\xd0'): 29,
  (29, '\xd1'): 29,
  (29, '\xd2'): 29,
  (29, '\xd3'): 29,
  (29, '\xd4'): 29,
  (29, '\xd5'): 29,
  (29, '\xd6'): 29,
  (29, '\xd7'): 29,
  (29, '\xd8'): 29,
  (29, '\xd9'): 29,
  (29, '\xda'): 29,
  (29, '\xdb'): 29,
  (29, '\xdc'): 29,
  (29, '\xdd'): 29,
  (29, '\xde'): 29,
  (29, '\xdf'): 29,
  (29, '\xe0'): 29,
  (29, '\xe1'): 29,
  (29, '\xe2'): 29,
  (29, '\xe3'): 29,
  (29, '\xe4'): 29,
  (29, '\xe5'): 29,
  (29, '\xe6'): 29,
  (29, '\xe7'): 29,
  (29, '\xe8'): 29,
  (29, '\xe9'): 29,
  (29, '\xea'): 29,
  (29, '\xeb'): 29,
  (29, '\xec'): 29,
  (29, '\xed'): 29,
  (29, '\xee'): 29,
  (29, '\xef'): 29,
  (29, '\xf0'): 29,
  (29, '\xf1'): 29,
  (29, '\xf2'): 29,
  (29, '\xf3'): 29,
  (29, '\xf4'): 29,
  (29, '\xf5'): 29,
  (29, '\xf6'): 29,
  (29, '\xf7'): 29,
  (29, '\xf8'): 29,
  (29, '\xf9'): 29,
  (29, '\xfa'): 29,
  (29, '\xfb'): 29,
  (29, '\xfc'): 29,
  (29, '\xfd'): 29,
  (29, '\xfe'): 29,
  (29, '\xff'): 29,
  (31, '-'): 50,
  (31, '>'): 51,
  (32, '.'): 42,
  (32, ':'): 43,
  (32, '<'): 41,
  (32, '='): 44,
  (32, '@'): 40,
  (32, '\\'): 45,
  (34, '0'): 10,
  (34, '1'): 10,
  (34, '2'): 10,
  (34, '3'): 10,
  (34, '4'): 10,
  (34, '5'): 10,
  (34, '6'): 10,
  (34, '7'): 10,
  (34, '8'): 10,
  (34, '9'): 10,
  (34, 'A'): 10,
  (34, 'B'): 10,
  (34, 'C'): 10,
  (34, 'D'): 10,
  (34, 'E'): 10,
  (34, 'F'): 10,
  (34, 'G'): 10,
  (34, 'H'): 10,
  (34, 'I'): 10,
  (34, 'J'): 10,
  (34, 'K'): 10,
  (34, 'L'): 10,
  (34, 'M'): 10,
  (34, 'N'): 10,
  (34, 'O'): 10,
  (34, 'P'): 10,
  (34, 'Q'): 10,
  (34, 'R'): 10,
  (34, 'S'): 10,
  (34, 'T'): 10,
  (34, 'U'): 10,
  (34, 'V'): 10,
  (34, 'W'): 10,
  (34, 'X'): 10,
  (34, 'Y'): 10,
  (34, 'Z'): 10,
  (34, '_'): 10,
  (34, 'a'): 10,
  (34, 'b'): 10,
  (34, 'c'): 10,
  (34, 'd'): 10,
  (34, 'e'): 10,
  (34, 'f'): 10,
  (34, 'g'): 10,
  (34, 'h'): 10,
  (34, 'i'): 10,
  (34, 'j'): 10,
  (34, 'k'): 10,
  (34, 'l'): 10,
  (34, 'm'): 10,
  (34, 'n'): 10,
  (34, 'o'): 10,
  (34, 'p'): 10,
  (34, 'q'): 10,
  (34, 'r'): 10,
  (34, 's'): 39,
  (34, 't'): 10,
  (34, 'u'): 10,
  (34, 'v'): 10,
  (34, 'w'): 10,
  (34, 'x'): 10,
  (34, 'y'): 10,
  (34, 'z'): 10,
  (35, '0'): 10,
  (35, '1'): 10,
  (35, '2'): 10,
  (35, '3'): 10,
  (35, '4'): 10,
  (35, '5'): 10,
  (35, '6'): 10,
  (35, '7'): 10,
  (35, '8'): 10,
  (35, '9'): 10,
  (35, 'A'): 10,
  (35, 'B'): 10,
  (35, 'C'): 10,
  (35, 'D'): 10,
  (35, 'E'): 10,
  (35, 'F'): 10,
  (35, 'G'): 10,
  (35, 'H'): 10,
  (35, 'I'): 10,
  (35, 'J'): 10,
  (35, 'K'): 10,
  (35, 'L'): 10,
  (35, 'M'): 10,
  (35, 'N'): 10,
  (35, 'O'): 10,
  (35, 'P'): 10,
  (35, 'Q'): 10,
  (35, 'R'): 10,
  (35, 'S'): 10,
  (35, 'T'): 10,
  (35, 'U'): 10,
  (35, 'V'): 10,
  (35, 'W'): 10,
  (35, 'X'): 10,
  (35, 'Y'): 10,
  (35, 'Z'): 10,
  (35, '_'): 10,
  (35, 'a'): 10,
  (35, 'b'): 10,
  (35, 'c'): 10,
  (35, 'd'): 10,
  (35, 'e'): 10,
  (35, 'f'): 10,
  (35, 'g'): 10,
  (35, 'h'): 10,
  (35, 'i'): 10,
  (35, 'j'): 10,
  (35, 'k'): 10,
  (35, 'l'): 10,
  (35, 'm'): 10,
  (35, 'n'): 10,
  (35, 'o'): 37,
  (35, 'p'): 10,
  (35, 'q'): 10,
  (35, 'r'): 10,
  (35, 's'): 10,
  (35, 't'): 10,
  (35, 'u'): 10,
  (35, 'v'): 10,
  (35, 'w'): 10,
  (35, 'x'): 10,
  (35, 'y'): 10,
  (35, 'z'): 10,
  (37, '0'): 10,
  (37, '1'): 10,
  (37, '2'): 10,
  (37, '3'): 10,
  (37, '4'): 10,
  (37, '5'): 10,
  (37, '6'): 10,
  (37, '7'): 10,
  (37, '8'): 10,
  (37, '9'): 10,
  (37, 'A'): 10,
  (37, 'B'): 10,
  (37, 'C'): 10,
  (37, 'D'): 10,
  (37, 'E'): 10,
  (37, 'F'): 10,
  (37, 'G'): 10,
  (37, 'H'): 10,
  (37, 'I'): 10,
  (37, 'J'): 10,
  (37, 'K'): 10,
  (37, 'L'): 10,
  (37, 'M'): 10,
  (37, 'N'): 10,
  (37, 'O'): 10,
  (37, 'P'): 10,
  (37, 'Q'): 10,
  (37, 'R'): 10,
  (37, 'S'): 10,
  (37, 'T'): 10,
  (37, 'U'): 10,
  (37, 'V'): 10,
  (37, 'W'): 10,
  (37, 'X'): 10,
  (37, 'Y'): 10,
  (37, 'Z'): 10,
  (37, '_'): 10,
  (37, 'a'): 10,
  (37, 'b'): 10,
  (37, 'c'): 10,
  (37, 'd'): 38,
  (37, 'e'): 10,
  (37, 'f'): 10,
  (37, 'g'): 10,
  (37, 'h'): 10,
  (37, 'i'): 10,
  (37, 'j'): 10,
  (37, 'k'): 10,
  (37, 'l'): 10,
  (37, 'm'): 10,
  (37, 'n'): 10,
  (37, 'o'): 10,
  (37, 'p'): 10,
  (37, 'q'): 10,
  (37, 'r'): 10,
  (37, 's'): 10,
  (37, 't'): 10,
  (37, 'u'): 10,
  (37, 'v'): 10,
  (37, 'w'): 10,
  (37, 'x'): 10,
  (37, 'y'): 10,
  (37, 'z'): 10,
  (38, '0'): 10,
  (38, '1'): 10,
  (38, '2'): 10,
  (38, '3'): 10,
  (38, '4'): 10,
  (38, '5'): 10,
  (38, '6'): 10,
  (38, '7'): 10,
  (38, '8'): 10,
  (38, '9'): 10,
  (38, 'A'): 10,
  (38, 'B'): 10,
  (38, 'C'): 10,
  (38, 'D'): 10,
  (38, 'E'): 10,
  (38, 'F'): 10,
  (38, 'G'): 10,
  (38, 'H'): 10,
  (38, 'I'): 10,
  (38, 'J'): 10,
  (38, 'K'): 10,
  (38, 'L'): 10,
  (38, 'M'): 10,
  (38, 'N'): 10,
  (38, 'O'): 10,
  (38, 'P'): 10,
  (38, 'Q'): 10,
  (38, 'R'): 10,
  (38, 'S'): 10,
  (38, 'T'): 10,
  (38, 'U'): 10,
  (38, 'V'): 10,
  (38, 'W'): 10,
  (38, 'X'): 10,
  (38, 'Y'): 10,
  (38, 'Z'): 10,
  (38, '_'): 10,
  (38, 'a'): 10,
  (38, 'b'): 10,
  (38, 'c'): 10,
  (38, 'd'): 10,
  (38, 'e'): 10,
  (38, 'f'): 10,
  (38, 'g'): 10,
  (38, 'h'): 10,
  (38, 'i'): 10,
  (38, 'j'): 10,
  (38, 'k'): 10,
  (38, 'l'): 10,
  (38, 'm'): 10,
  (38, 'n'): 10,
  (38, 'o'): 10,
  (38, 'p'): 10,
  (38, 'q'): 10,
  (38, 'r'): 10,
  (38, 's'): 10,
  (38, 't'): 10,
  (38, 'u'): 10,
  (38, 'v'): 10,
  (38, 'w'): 10,
  (38, 'x'): 10,
  (38, 'y'): 10,
  (38, 'z'): 10,
  (39, '0'): 10,
  (39, '1'): 10,
  (39, '2'): 10,
  (39, '3'): 10,
  (39, '4'): 10,
  (39, '5'): 10,
  (39, '6'): 10,
  (39, '7'): 10,
  (39, '8'): 10,
  (39, '9'): 10,
  (39, 'A'): 10,
  (39, 'B'): 10,
  (39, 'C'): 10,
  (39, 'D'): 10,
  (39, 'E'): 10,
  (39, 'F'): 10,
  (39, 'G'): 10,
  (39, 'H'): 10,
  (39, 'I'): 10,
  (39, 'J'): 10,
  (39, 'K'): 10,
  (39, 'L'): 10,
  (39, 'M'): 10,
  (39, 'N'): 10,
  (39, 'O'): 10,
  (39, 'P'): 10,
  (39, 'Q'): 10,
  (39, 'R'): 10,
  (39, 'S'): 10,
  (39, 'T'): 10,
  (39, 'U'): 10,
  (39, 'V'): 10,
  (39, 'W'): 10,
  (39, 'X'): 10,
  (39, 'Y'): 10,
  (39, 'Z'): 10,
  (39, '_'): 10,
  (39, 'a'): 10,
  (39, 'b'): 10,
  (39, 'c'): 10,
  (39, 'd'): 10,
  (39, 'e'): 10,
  (39, 'f'): 10,
  (39, 'g'): 10,
  (39, 'h'): 10,
  (39, 'i'): 10,
  (39, 'j'): 10,
  (39, 'k'): 10,
  (39, 'l'): 10,
  (39, 'm'): 10,
  (39, 'n'): 10,
  (39, 'o'): 10,
  (39, 'p'): 10,
  (39, 'q'): 10,
  (39, 'r'): 10,
  (39, 's'): 10,
  (39, 't'): 10,
  (39, 'u'): 10,
  (39, 'v'): 10,
  (39, 'w'): 10,
  (39, 'x'): 10,
  (39, 'y'): 10,
  (39, 'z'): 10,
  (40, '='): 49,
  (42, '.'): 48,
  (43, '='): 47,
  (45, '='): 46,
  (50, '>'): 52,
  (53, '0'): 10,
  (53, '1'): 10,
  (53, '2'): 10,
  (53, '3'): 10,
  (53, '4'): 10,
  (53, '5'): 10,
  (53, '6'): 10,
  (53, '7'): 10,
  (53, '8'): 10,
  (53, '9'): 10,
  (53, 'A'): 10,
  (53, 'B'): 10,
  (53, 'C'): 10,
  (53, 'D'): 10,
  (53, 'E'): 10,
  (53, 'F'): 10,
  (53, 'G'): 10,
  (53, 'H'): 10,
  (53, 'I'): 10,
  (53, 'J'): 10,
  (53, 'K'): 10,
  (53, 'L'): 10,
  (53, 'M'): 10,
  (53, 'N'): 10,
  (53, 'O'): 10,
  (53, 'P'): 10,
  (53, 'Q'): 10,
  (53, 'R'): 10,
  (53, 'S'): 10,
  (53, 'T'): 10,
  (53, 'U'): 10,
  (53, 'V'): 10,
  (53, 'W'): 10,
  (53, 'X'): 10,
  (53, 'Y'): 10,
  (53, 'Z'): 10,
  (53, '_'): 10,
  (53, 'a'): 10,
  (53, 'b'): 10,
  (53, 'c'): 10,
  (53, 'd'): 10,
  (53, 'e'): 10,
  (53, 'f'): 10,
  (53, 'g'): 10,
  (53, 'h'): 10,
  (53, 'i'): 10,
  (53, 'j'): 10,
  (53, 'k'): 10,
  (53, 'l'): 10,
  (53, 'm'): 54,
  (53, 'n'): 10,
  (53, 'o'): 10,
  (53, 'p'): 10,
  (53, 'q'): 10,
  (53, 'r'): 10,
  (53, 's'): 10,
  (53, 't'): 10,
  (53, 'u'): 10,
  (53, 'v'): 10,
  (53, 'w'): 10,
  (53, 'x'): 10,
  (53, 'y'): 10,
  (53, 'z'): 10,
  (54, '0'): 10,
  (54, '1'): 10,
  (54, '2'): 10,
  (54, '3'): 10,
  (54, '4'): 10,
  (54, '5'): 10,
  (54, '6'): 10,
  (54, '7'): 10,
  (54, '8'): 10,
  (54, '9'): 10,
  (54, 'A'): 10,
  (54, 'B'): 10,
  (54, 'C'): 10,
  (54, 'D'): 10,
  (54, 'E'): 10,
  (54, 'F'): 10,
  (54, 'G'): 10,
  (54, 'H'): 10,
  (54, 'I'): 10,
  (54, 'J'): 10,
  (54, 'K'): 10,
  (54, 'L'): 10,
  (54, 'M'): 10,
  (54, 'N'): 10,
  (54, 'O'): 10,
  (54, 'P'): 10,
  (54, 'Q'): 10,
  (54, 'R'): 10,
  (54, 'S'): 10,
  (54, 'T'): 10,
  (54, 'U'): 10,
  (54, 'V'): 10,
  (54, 'W'): 10,
  (54, 'X'): 10,
  (54, 'Y'): 10,
  (54, 'Z'): 10,
  (54, '_'): 10,
  (54, 'a'): 10,
  (54, 'b'): 10,
  (54, 'c'): 10,
  (54, 'd'): 10,
  (54, 'e'): 10,
  (54, 'f'): 10,
  (54, 'g'): 10,
  (54, 'h'): 10,
  (54, 'i'): 10,
  (54, 'j'): 10,
  (54, 'k'): 10,
  (54, 'l'): 10,
  (54, 'm'): 10,
  (54, 'n'): 10,
  (54, 'o'): 10,
  (54, 'p'): 10,
  (54, 'q'): 10,
  (54, 'r'): 10,
  (54, 's'): 10,
  (54, 't'): 10,
  (54, 'u'): 10,
  (54, 'v'): 10,
  (54, 'w'): 10,
  (54, 'x'): 10,
  (54, 'y'): 10,
  (54, 'z'): 10,
  (61, '\x00'): 61,
  (61, '\x01'): 61,
  (61, '\x02'): 61,
  (61, '\x03'): 61,
  (61, '\x04'): 61,
  (61, '\x05'): 61,
  (61, '\x06'): 61,
  (61, '\x07'): 61,
  (61, '\x08'): 61,
  (61, '\t'): 61,
  (61, '\n'): 61,
  (61, '\x0b'): 61,
  (61, '\x0c'): 61,
  (61, '\r'): 61,
  (61, '\x0e'): 61,
  (61, '\x0f'): 61,
  (61, '\x10'): 61,
  (61, '\x11'): 61,
  (61, '\x12'): 61,
  (61, '\x13'): 61,
  (61, '\x14'): 61,
  (61, '\x15'): 61,
  (61, '\x16'): 61,
  (61, '\x17'): 61,
  (61, '\x18'): 61,
  (61, '\x19'): 61,
  (61, '\x1a'): 61,
  (61, '\x1b'): 61,
  (61, '\x1c'): 61,
  (61, '\x1d'): 61,
  (61, '\x1e'): 61,
  (61, '\x1f'): 61,
  (61, ' '): 61,
  (61, '!'): 61,
  (61, '"'): 61,
  (61, '#'): 61,
  (61, '$'): 61,
  (61, '%'): 61,
  (61, '&'): 61,
  (61, "'"): 61,
  (61, '('): 61,
  (61, ')'): 61,
  (61, '*'): 64,
  (61, '+'): 61,
  (61, ','): 61,
  (61, '-'): 61,
  (61, '.'): 61,
  (61, '/'): 61,
  (61, '0'): 61,
  (61, '1'): 61,
  (61, '2'): 61,
  (61, '3'): 61,
  (61, '4'): 61,
  (61, '5'): 61,
  (61, '6'): 61,
  (61, '7'): 61,
  (61, '8'): 61,
  (61, '9'): 61,
  (61, ':'): 61,
  (61, ';'): 61,
  (61, '<'): 61,
  (61, '='): 61,
  (61, '>'): 61,
  (61, '?'): 61,
  (61, '@'): 61,
  (61, 'A'): 61,
  (61, 'B'): 61,
  (61, 'C'): 61,
  (61, 'D'): 61,
  (61, 'E'): 61,
  (61, 'F'): 61,
  (61, 'G'): 61,
  (61, 'H'): 61,
  (61, 'I'): 61,
  (61, 'J'): 61,
  (61, 'K'): 61,
  (61, 'L'): 61,
  (61, 'M'): 61,
  (61, 'N'): 61,
  (61, 'O'): 61,
  (61, 'P'): 61,
  (61, 'Q'): 61,
  (61, 'R'): 61,
  (61, 'S'): 61,
  (61, 'T'): 61,
  (61, 'U'): 61,
  (61, 'V'): 61,
  (61, 'W'): 61,
  (61, 'X'): 61,
  (61, 'Y'): 61,
  (61, 'Z'): 61,
  (61, '['): 61,
  (61, '\\'): 61,
  (61, ']'): 61,
  (61, '^'): 61,
  (61, '_'): 61,
  (61, '`'): 61,
  (61, 'a'): 61,
  (61, 'b'): 61,
  (61, 'c'): 61,
  (61, 'd'): 61,
  (61, 'e'): 61,
  (61, 'f'): 61,
  (61, 'g'): 61,
  (61, 'h'): 61,
  (61, 'i'): 61,
  (61, 'j'): 61,
  (61, 'k'): 61,
  (61, 'l'): 61,
  (61, 'm'): 61,
  (61, 'n'): 61,
  (61, 'o'): 61,
  (61, 'p'): 61,
  (61, 'q'): 61,
  (61, 'r'): 61,
  (61, 's'): 61,
  (61, 't'): 61,
  (61, 'u'): 61,
  (61, 'v'): 61,
  (61, 'w'): 61,
  (61, 'x'): 61,
  (61, 'y'): 61,
  (61, 'z'): 61,
  (61, '{'): 61,
  (61, '|'): 61,
  (61, '}'): 61,
  (61, '~'): 61,
  (61, '\x7f'): 61,
  (61, '\x80'): 61,
  (61, '\x81'): 61,
  (61, '\x82'): 61,
  (61, '\x83'): 61,
  (61, '\x84'): 61,
  (61, '\x85'): 61,
  (61, '\x86'): 61,
  (61, '\x87'): 61,
  (61, '\x88'): 61,
  (61, '\x89'): 61,
  (61, '\x8a'): 61,
  (61, '\x8b'): 61,
  (61, '\x8c'): 61,
  (61, '\x8d'): 61,
  (61, '\x8e'): 61,
  (61, '\x8f'): 61,
  (61, '\x90'): 61,
  (61, '\x91'): 61,
  (61, '\x92'): 61,
  (61, '\x93'): 61,
  (61, '\x94'): 61,
  (61, '\x95'): 61,
  (61, '\x96'): 61,
  (61, '\x97'): 61,
  (61, '\x98'): 61,
  (61, '\x99'): 61,
  (61, '\x9a'): 61,
  (61, '\x9b'): 61,
  (61, '\x9c'): 61,
  (61, '\x9d'): 61,
  (61, '\x9e'): 61,
  (61, '\x9f'): 61,
  (61, '\xa0'): 61,
  (61, '\xa1'): 61,
  (61, '\xa2'): 61,
  (61, '\xa3'): 61,
  (61, '\xa4'): 61,
  (61, '\xa5'): 61,
  (61, '\xa6'): 61,
  (61, '\xa7'): 61,
  (61, '\xa8'): 61,
  (61, '\xa9'): 61,
  (61, '\xaa'): 61,
  (61, '\xab'): 61,
  (61, '\xac'): 61,
  (61, '\xad'): 61,
  (61, '\xae'): 61,
  (61, '\xaf'): 61,
  (61, '\xb0'): 61,
  (61, '\xb1'): 61,
  (61, '\xb2'): 61,
  (61, '\xb3'): 61,
  (61, '\xb4'): 61,
  (61, '\xb5'): 61,
  (61, '\xb6'): 61,
  (61, '\xb7'): 61,
  (61, '\xb8'): 61,
  (61, '\xb9'): 61,
  (61, '\xba'): 61,
  (61, '\xbb'): 61,
  (61, '\xbc'): 61,
  (61, '\xbd'): 61,
  (61, '\xbe'): 61,
  (61, '\xbf'): 61,
  (61, '\xc0'): 61,
  (61, '\xc1'): 61,
  (61, '\xc2'): 61,
  (61, '\xc3'): 61,
  (61, '\xc4'): 61,
  (61, '\xc5'): 61,
  (61, '\xc6'): 61,
  (61, '\xc7'): 61,
  (61, '\xc8'): 61,
  (61, '\xc9'): 61,
  (61, '\xca'): 61,
  (61, '\xcb'): 61,
  (61, '\xcc'): 61,
  (61, '\xcd'): 61,
  (61, '\xce'): 61,
  (61, '\xcf'): 61,
  (61, '\xd0'): 61,
  (61, '\xd1'): 61,
  (61, '\xd2'): 61,
  (61, '\xd3'): 61,
  (61, '\xd4'): 61,
  (61, '\xd5'): 61,
  (61, '\xd6'): 61,
  (61, '\xd7'): 61,
  (61, '\xd8'): 61,
  (61, '\xd9'): 61,
  (61, '\xda'): 61,
  (61, '\xdb'): 61,
  (61, '\xdc'): 61,
  (61, '\xdd'): 61,
  (61, '\xde'): 61,
  (61, '\xdf'): 61,
  (61, '\xe0'): 61,
  (61, '\xe1'): 61,
  (61, '\xe2'): 61,
  (61, '\xe3'): 61,
  (61, '\xe4'): 61,
  (61, '\xe5'): 61,
  (61, '\xe6'): 61,
  (61, '\xe7'): 61,
  (61, '\xe8'): 61,
  (61, '\xe9'): 61,
  (61, '\xea'): 61,
  (61, '\xeb'): 61,
  (61, '\xec'): 61,
  (61, '\xed'): 61,
  (61, '\xee'): 61,
  (61, '\xef'): 61,
  (61, '\xf0'): 61,
  (61, '\xf1'): 61,
  (61, '\xf2'): 61,
  (61, '\xf3'): 61,
  (61, '\xf4'): 61,
  (61, '\xf5'): 61,
  (61, '\xf6'): 61,
  (61, '\xf7'): 61,
  (61, '\xf8'): 61,
  (61, '\xf9'): 61,
  (61, '\xfa'): 61,
  (61, '\xfb'): 61,
  (61, '\xfc'): 61,
  (61, '\xfd'): 61,
  (61, '\xfe'): 61,
  (61, '\xff'): 61,
  (64, '\x00'): 61,
  (64, '\x01'): 61,
  (64, '\x02'): 61,
  (64, '\x03'): 61,
  (64, '\x04'): 61,
  (64, '\x05'): 61,
  (64, '\x06'): 61,
  (64, '\x07'): 61,
  (64, '\x08'): 61,
  (64, '\t'): 61,
  (64, '\n'): 61,
  (64, '\x0b'): 61,
  (64, '\x0c'): 61,
  (64, '\r'): 61,
  (64, '\x0e'): 61,
  (64, '\x0f'): 61,
  (64, '\x10'): 61,
  (64, '\x11'): 61,
  (64, '\x12'): 61,
  (64, '\x13'): 61,
  (64, '\x14'): 61,
  (64, '\x15'): 61,
  (64, '\x16'): 61,
  (64, '\x17'): 61,
  (64, '\x18'): 61,
  (64, '\x19'): 61,
  (64, '\x1a'): 61,
  (64, '\x1b'): 61,
  (64, '\x1c'): 61,
  (64, '\x1d'): 61,
  (64, '\x1e'): 61,
  (64, '\x1f'): 61,
  (64, ' '): 61,
  (64, '!'): 61,
  (64, '"'): 61,
  (64, '#'): 61,
  (64, '$'): 61,
  (64, '%'): 61,
  (64, '&'): 61,
  (64, "'"): 61,
  (64, '('): 61,
  (64, ')'): 61,
  (64, '*'): 61,
  (64, '+'): 61,
  (64, ','): 61,
  (64, '-'): 61,
  (64, '.'): 61,
  (64, '/'): 1,
  (64, '0'): 61,
  (64, '1'): 61,
  (64, '2'): 61,
  (64, '3'): 61,
  (64, '4'): 61,
  (64, '5'): 61,
  (64, '6'): 61,
  (64, '7'): 61,
  (64, '8'): 61,
  (64, '9'): 61,
  (64, ':'): 61,
  (64, ';'): 61,
  (64, '<'): 61,
  (64, '='): 61,
  (64, '>'): 61,
  (64, '?'): 61,
  (64, '@'): 61,
  (64, 'A'): 61,
  (64, 'B'): 61,
  (64, 'C'): 61,
  (64, 'D'): 61,
  (64, 'E'): 61,
  (64, 'F'): 61,
  (64, 'G'): 61,
  (64, 'H'): 61,
  (64, 'I'): 61,
  (64, 'J'): 61,
  (64, 'K'): 61,
  (64, 'L'): 61,
  (64, 'M'): 61,
  (64, 'N'): 61,
  (64, 'O'): 61,
  (64, 'P'): 61,
  (64, 'Q'): 61,
  (64, 'R'): 61,
  (64, 'S'): 61,
  (64, 'T'): 61,
  (64, 'U'): 61,
  (64, 'V'): 61,
  (64, 'W'): 61,
  (64, 'X'): 61,
  (64, 'Y'): 61,
  (64, 'Z'): 61,
  (64, '['): 61,
  (64, '\\'): 61,
  (64, ']'): 61,
  (64, '^'): 61,
  (64, '_'): 61,
  (64, '`'): 61,
  (64, 'a'): 61,
  (64, 'b'): 61,
  (64, 'c'): 61,
  (64, 'd'): 61,
  (64, 'e'): 61,
  (64, 'f'): 61,
  (64, 'g'): 61,
  (64, 'h'): 61,
  (64, 'i'): 61,
  (64, 'j'): 61,
  (64, 'k'): 61,
  (64, 'l'): 61,
  (64, 'm'): 61,
  (64, 'n'): 61,
  (64, 'o'): 61,
  (64, 'p'): 61,
  (64, 'q'): 61,
  (64, 'r'): 61,
  (64, 's'): 61,
  (64, 't'): 61,
  (64, 'u'): 61,
  (64, 'v'): 61,
  (64, 'w'): 61,
  (64, 'x'): 61,
  (64, 'y'): 61,
  (64, 'z'): 61,
  (64, '{'): 61,
  (64, '|'): 61,
  (64, '}'): 61,
  (64, '~'): 61,
  (64, '\x7f'): 61,
  (64, '\x80'): 61,
  (64, '\x81'): 61,
  (64, '\x82'): 61,
  (64, '\x83'): 61,
  (64, '\x84'): 61,
  (64, '\x85'): 61,
  (64, '\x86'): 61,
  (64, '\x87'): 61,
  (64, '\x88'): 61,
  (64, '\x89'): 61,
  (64, '\x8a'): 61,
  (64, '\x8b'): 61,
  (64, '\x8c'): 61,
  (64, '\x8d'): 61,
  (64, '\x8e'): 61,
  (64, '\x8f'): 61,
  (64, '\x90'): 61,
  (64, '\x91'): 61,
  (64, '\x92'): 61,
  (64, '\x93'): 61,
  (64, '\x94'): 61,
  (64, '\x95'): 61,
  (64, '\x96'): 61,
  (64, '\x97'): 61,
  (64, '\x98'): 61,
  (64, '\x99'): 61,
  (64, '\x9a'): 61,
  (64, '\x9b'): 61,
  (64, '\x9c'): 61,
  (64, '\x9d'): 61,
  (64, '\x9e'): 61,
  (64, '\x9f'): 61,
  (64, '\xa0'): 61,
  (64, '\xa1'): 61,
  (64, '\xa2'): 61,
  (64, '\xa3'): 61,
  (64, '\xa4'): 61,
  (64, '\xa5'): 61,
  (64, '\xa6'): 61,
  (64, '\xa7'): 61,
  (64, '\xa8'): 61,
  (64, '\xa9'): 61,
  (64, '\xaa'): 61,
  (64, '\xab'): 61,
  (64, '\xac'): 61,
  (64, '\xad'): 61,
  (64, '\xae'): 61,
  (64, '\xaf'): 61,
  (64, '\xb0'): 61,
  (64, '\xb1'): 61,
  (64, '\xb2'): 61,
  (64, '\xb3'): 61,
  (64, '\xb4'): 61,
  (64, '\xb5'): 61,
  (64, '\xb6'): 61,
  (64, '\xb7'): 61,
  (64, '\xb8'): 61,
  (64, '\xb9'): 61,
  (64, '\xba'): 61,
  (64, '\xbb'): 61,
  (64, '\xbc'): 61,
  (64, '\xbd'): 61,
  (64, '\xbe'): 61,
  (64, '\xbf'): 61,
  (64, '\xc0'): 61,
  (64, '\xc1'): 61,
  (64, '\xc2'): 61,
  (64, '\xc3'): 61,
  (64, '\xc4'): 61,
  (64, '\xc5'): 61,
  (64, '\xc6'): 61,
  (64, '\xc7'): 61,
  (64, '\xc8'): 61,
  (64, '\xc9'): 61,
  (64, '\xca'): 61,
  (64, '\xcb'): 61,
  (64, '\xcc'): 61,
  (64, '\xcd'): 61,
  (64, '\xce'): 61,
  (64, '\xcf'): 61,
  (64, '\xd0'): 61,
  (64, '\xd1'): 61,
  (64, '\xd2'): 61,
  (64, '\xd3'): 61,
  (64, '\xd4'): 61,
  (64, '\xd5'): 61,
  (64, '\xd6'): 61,
  (64, '\xd7'): 61,
  (64, '\xd8'): 61,
  (64, '\xd9'): 61,
  (64, '\xda'): 61,
  (64, '\xdb'): 61,
  (64, '\xdc'): 61,
  (64, '\xdd'): 61,
  (64, '\xde'): 61,
  (64, '\xdf'): 61,
  (64, '\xe0'): 61,
  (64, '\xe1'): 61,
  (64, '\xe2'): 61,
  (64, '\xe3'): 61,
  (64, '\xe4'): 61,
  (64, '\xe5'): 61,
  (64, '\xe6'): 61,
  (64, '\xe7'): 61,
  (64, '\xe8'): 61,
  (64, '\xe9'): 61,
  (64, '\xea'): 61,
  (64, '\xeb'): 61,
  (64, '\xec'): 61,
  (64, '\xed'): 61,
  (64, '\xee'): 61,
  (64, '\xef'): 61,
  (64, '\xf0'): 61,
  (64, '\xf1'): 61,
  (64, '\xf2'): 61,
  (64, '\xf3'): 61,
  (64, '\xf4'): 61,
  (64, '\xf5'): 61,
  (64, '\xf6'): 61,
  (64, '\xf7'): 61,
  (64, '\xf8'): 61,
  (64, '\xf9'): 61,
  (64, '\xfa'): 61,
  (64, '\xfb'): 61,
  (64, '\xfc'): 61,
  (64, '\xfd'): 61,
  (64, '\xfe'): 61,
  (64, '\xff'): 61,
  (65, '0'): 10,
  (65, '1'): 10,
  (65, '2'): 10,
  (65, '3'): 10,
  (65, '4'): 10,
  (65, '5'): 10,
  (65, '6'): 10,
  (65, '7'): 10,
  (65, '8'): 10,
  (65, '9'): 10,
  (65, 'A'): 10,
  (65, 'B'): 10,
  (65, 'C'): 10,
  (65, 'D'): 10,
  (65, 'E'): 10,
  (65, 'F'): 10,
  (65, 'G'): 10,
  (65, 'H'): 10,
  (65, 'I'): 10,
  (65, 'J'): 10,
  (65, 'K'): 10,
  (65, 'L'): 10,
  (65, 'M'): 10,
  (65, 'N'): 10,
  (65, 'O'): 10,
  (65, 'P'): 10,
  (65, 'Q'): 10,
  (65, 'R'): 10,
  (65, 'S'): 10,
  (65, 'T'): 10,
  (65, 'U'): 10,
  (65, 'V'): 10,
  (65, 'W'): 10,
  (65, 'X'): 10,
  (65, 'Y'): 10,
  (65, 'Z'): 10,
  (65, '_'): 10,
  (65, 'a'): 10,
  (65, 'b'): 10,
  (65, 'c'): 10,
  (65, 'd'): 10,
  (65, 'e'): 10,
  (65, 'f'): 10,
  (65, 'g'): 10,
  (65, 'h'): 10,
  (65, 'i'): 10,
  (65, 'j'): 10,
  (65, 'k'): 10,
  (65, 'l'): 10,
  (65, 'm'): 10,
  (65, 'n'): 10,
  (65, 'o'): 10,
  (65, 'p'): 10,
  (65, 'q'): 10,
  (65, 'r'): 66,
  (65, 's'): 10,
  (65, 't'): 10,
  (65, 'u'): 10,
  (65, 'v'): 10,
  (65, 'w'): 10,
  (65, 'x'): 10,
  (65, 'y'): 10,
  (65, 'z'): 10,
  (66, '0'): 10,
  (66, '1'): 10,
  (66, '2'): 10,
  (66, '3'): 10,
  (66, '4'): 10,
  (66, '5'): 10,
  (66, '6'): 10,
  (66, '7'): 10,
  (66, '8'): 10,
  (66, '9'): 10,
  (66, 'A'): 10,
  (66, 'B'): 10,
  (66, 'C'): 10,
  (66, 'D'): 10,
  (66, 'E'): 10,
  (66, 'F'): 10,
  (66, 'G'): 10,
  (66, 'H'): 10,
  (66, 'I'): 10,
  (66, 'J'): 10,
  (66, 'K'): 10,
  (66, 'L'): 10,
  (66, 'M'): 10,
  (66, 'N'): 10,
  (66, 'O'): 10,
  (66, 'P'): 10,
  (66, 'Q'): 10,
  (66, 'R'): 10,
  (66, 'S'): 10,
  (66, 'T'): 10,
  (66, 'U'): 10,
  (66, 'V'): 10,
  (66, 'W'): 10,
  (66, 'X'): 10,
  (66, 'Y'): 10,
  (66, 'Z'): 10,
  (66, '_'): 10,
  (66, 'a'): 10,
  (66, 'b'): 10,
  (66, 'c'): 10,
  (66, 'd'): 10,
  (66, 'e'): 10,
  (66, 'f'): 10,
  (66, 'g'): 10,
  (66, 'h'): 10,
  (66, 'i'): 10,
  (66, 'j'): 10,
  (66, 'k'): 10,
  (66, 'l'): 10,
  (66, 'm'): 10,
  (66, 'n'): 10,
  (66, 'o'): 10,
  (66, 'p'): 10,
  (66, 'q'): 10,
  (66, 'r'): 10,
  (66, 's'): 10,
  (66, 't'): 10,
  (66, 'u'): 10,
  (66, 'v'): 10,
  (66, 'w'): 10,
  (66, 'x'): 10,
  (66, 'y'): 10,
  (66, 'z'): 10,
  (68, '='): 70,
  (71, '<'): 75,
  (73, '='): 74,
  (77, '0'): 78,
  (77, '1'): 78,
  (77, '2'): 78,
  (77, '3'): 78,
  (77, '4'): 78,
  (77, '5'): 78,
  (77, '6'): 78,
  (77, '7'): 78,
  (77, '8'): 78,
  (77, '9'): 78,
  (78, '0'): 78,
  (78, '1'): 78,
  (78, '2'): 78,
  (78, '3'): 78,
  (78, '4'): 78,
  (78, '5'): 78,
  (78, '6'): 78,
  (78, '7'): 78,
  (78, '8'): 78,
  (78, '9'): 78},
 set([1,
      2,
      3,
      4,
      5,
      6,
      8,
      9,
      10,
      11,
      12,
      14,
      15,
      16,
      17,
      18,
      19,
      21,
      22,
      23,
      24,
      25,
      26,
      27,
      28,
      29,
      30,
      31,
      32,
      33,
      34,
      35,
      36,
      37,
      38,
      39,
      41,
      44,
      46,
      47,
      48,
      49,
      51,
      52,
      53,
      54,
      55,
      56,
      57,
      58,
      59,
      60,
      62,
      63,
      65,
      66,
      67,
      68,
      69,
      70,
      72,
      73,
      74,
      75,
      76,
      78]),
 set([1,
      2,
      3,
      4,
      5,
      6,
      8,
      9,
      10,
      11,
      12,
      14,
      15,
      16,
      17,
      18,
      19,
      21,
      22,
      23,
      24,
      25,
      26,
      27,
      28,
      29,
      30,
      31,
      32,
      33,
      34,
      35,
      36,
      37,
      38,
      39,
      41,
      44,
      46,
      47,
      48,
      49,
      51,
      52,
      53,
      54,
      55,
      56,
      57,
      58,
      59,
      60,
      62,
      63,
      65,
      66,
      67,
      68,
      69,
      70,
      72,
      73,
      74,
      75,
      76,
      78]),
 ['0, 0, 0, 0, start|, 0, start|, 0, 0, 0, 0, start|, 0, 0, 0, 0, 0, start|, 0, start|, 0, 0, start|, 0, 0, 0, 0, 0, 0, start|, 0, start|, start|, 0, 0, start|, 0, start|, start|, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0',
  'IGNORE',
  '(',
  'ATOM',
  'NUMBER',
  'NUMBER',
  'ATOM',
  '1, 1, 1, 1',
  'VAR',
  'ATOM',
  'ATOM',
  'ATOM',
  '|',
  '0, start|, 0, final*, start*, 0, 1, final*, 0, final|, start|, 0, 1, final*, start*, 0, final*, 0, 1, final|, start|, 0, final*, start*, 0, final*',
  'ATOM',
  'ATOM',
  'ATOM',
  'ATOM',
  '[',
  '{',
  '1, final*, 0, start|, 0, final*, start*, 0, final*, 0, final|, start|, 0, 1, final*, start*, 0, final*, 0, 1, final|, start|, 0, final*, start*, 0',
  'ATOM',
  '.',
  'ATOM',
  'ATOM',
  'ATOM',
  'ATOM',
  'ATOM',
  'ATOM',
  'IGNORE',
  ')',
  'ATOM',
  'ATOM',
  ']',
  'ATOM',
  'ATOM',
  '}',
  'ATOM',
  'ATOM',
  'ATOM',
  '2',
  'ATOM',
  '2',
  '2',
  'ATOM',
  '2',
  'ATOM',
  'ATOM',
  'ATOM',
  'ATOM',
  '2',
  'ATOM',
  'ATOM',
  'ATOM',
  'ATOM',
  'ATOM',
  'ATOM',
  'ATOM',
  'ATOM',
  'STRING',
  'ATOM',
  'final*, start*, 2, final*, 0, start|, 0, 0, final*, start*, final*, 0, final*, start*, 0, final*, 0, final|, start|, 0, 1, final*, start*, final*, 0, final*, start*, 0, final*, 0, 1, final|, start|, 0, final*, start*, final*, 0, 1, final*, 0, start|, 0, final*, start*, final*, start*, 0, final*, 0, final*, final|, final*, 0, start|, 0, final*, start*, final*, start*, 0, final*, 0, final*, 1, final|, final*, 0, final|, start|, 0, 1, final*, start*, final*, start*, 0, final*, 0, final*, 0, 1, final|, start|, 0, final*, start*, final*, start*, 0, final*, 0',
  'ATOM',
  'ATOM',
  '0, final*, 1, 0, 1, 0, start|',
  'ATOM',
  'ATOM',
  'ATOM',
  'ATOM',
  'ATOM',
  'ATOM',
  '2',
  'ATOM',
  'ATOM',
  'ATOM',
  'ATOM',
  'ATOM',
  '1, 0',
  'NUMBER']), {'IGNORE': None})

# generated code between this line and its other occurence
 
if __name__ == '__main__':
    f = py.path.local(__file__)
    oldcontent = f.read()
    s = "# GENERATED CODE BETWEEN THIS LINE AND ITS OTHER OCCURENCE\n".lower()
    pre, gen, after = oldcontent.split(s)

    lexer, parser_fact, parser_query, basic_rules = make_all()
    newcontent = ("%s%s\nparser_fact = %r\nparser_query = %r\n%s\n"
                  "\n%s%s") % (
            pre, s, parser_fact, parser_query, lexer.get_dummy_repr(),
            s, after)
    print newcontent
    f.write(newcontent)
