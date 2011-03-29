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
         (1050, [("xfy", ["->"]),
                 ("fx",  ["block"])]),
         (1000, [("xfy", [","])]),
         (900,  [("fy",  ["\\+"]),
                 ("fx",  ["~"])]),
         (700,  [("xfx", ["<", "=", "=..", "=@=", "=:=", "=<", "==", "=\=", ">", "?=",
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
        e.modulewrapper.current_module = e.modulewrapper.user_module
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
  Rule('expr1050', [['expr1000', '->', 'expr1050', 'extraexpr1050'], ['block', 'expr1000', 'extraexpr1050'], ['expr1000', 'extraexpr1050']]),
  Rule('extraexpr1000', [[]]),
  Rule('expr1000', [['expr900', ',', 'expr1000', 'extraexpr1000'], ['expr900', 'extraexpr1000']]),
  Rule('extraexpr900', [[]]),
  Rule('expr900', [['\\+', 'expr900', 'extraexpr900'], ['~', 'expr700', 'extraexpr900'], ['expr700', 'extraexpr900']]),
  Rule('extraexpr700', [[]]),
  Rule('expr700', [['expr600', '<', 'expr600', 'extraexpr700'], ['expr600', '=', 'expr600', 'extraexpr700'], ['expr600', '=..', 'expr600', 'extraexpr700'], ['expr600', '=@=', 'expr600', 'extraexpr700'], ['expr600', '=:=', 'expr600', 'extraexpr700'], ['expr600', '=<', 'expr600', 'extraexpr700'], ['expr600', '==', 'expr600', 'extraexpr700'], ['expr600', '=\\=', 'expr600', 'extraexpr700'], ['expr600', '>', 'expr600', 'extraexpr700'], ['expr600', '?=', 'expr600', 'extraexpr700'], ['expr600', '>=', 'expr600', 'extraexpr700'], ['expr600', '@<', 'expr600', 'extraexpr700'], ['expr600', '@=<', 'expr600', 'extraexpr700'], ['expr600', '@>', 'expr600', 'extraexpr700'], ['expr600', '@>=', 'expr600', 'extraexpr700'], ['expr600', '\\=', 'expr600', 'extraexpr700'], ['expr600', '\\==', 'expr600', 'extraexpr700'], ['expr600', 'is', 'expr600', 'extraexpr700'], ['expr600', 'extraexpr700']]),
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
  Rule('expr1050', [['expr1000', '->', 'expr1050', 'extraexpr1050'], ['block', 'expr1000', 'extraexpr1050'], ['expr1000', 'extraexpr1050']]),
  Rule('extraexpr1000', [[]]),
  Rule('expr1000', [['expr900', ',', 'expr1000', 'extraexpr1000'], ['expr900', 'extraexpr1000']]),
  Rule('extraexpr900', [[]]),
  Rule('expr900', [['\\+', 'expr900', 'extraexpr900'], ['~', 'expr700', 'extraexpr900'], ['expr700', 'extraexpr900']]),
  Rule('extraexpr700', [[]]),
  Rule('expr700', [['expr600', '<', 'expr600', 'extraexpr700'], ['expr600', '=', 'expr600', 'extraexpr700'], ['expr600', '=..', 'expr600', 'extraexpr700'], ['expr600', '=@=', 'expr600', 'extraexpr700'], ['expr600', '=:=', 'expr600', 'extraexpr700'], ['expr600', '=<', 'expr600', 'extraexpr700'], ['expr600', '==', 'expr600', 'extraexpr700'], ['expr600', '=\\=', 'expr600', 'extraexpr700'], ['expr600', '>', 'expr600', 'extraexpr700'], ['expr600', '?=', 'expr600', 'extraexpr700'], ['expr600', '>=', 'expr600', 'extraexpr700'], ['expr600', '@<', 'expr600', 'extraexpr700'], ['expr600', '@=<', 'expr600', 'extraexpr700'], ['expr600', '@>', 'expr600', 'extraexpr700'], ['expr600', '@>=', 'expr600', 'extraexpr700'], ['expr600', '\\=', 'expr600', 'extraexpr700'], ['expr600', '\\==', 'expr600', 'extraexpr700'], ['expr600', 'is', 'expr600', 'extraexpr700'], ['expr600', 'extraexpr700']]),
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
            elif 'c' <= char <= 'h':
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
            elif char == 'a':
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
            elif char == 'b':
                state = 26
            elif char == 'r':
                state = 27
            elif char == '~':
                state = 28
            elif char == '!':
                state = 29
            elif char == '%':
                state = 30
            elif char == ')':
                state = 31
            elif char == '-':
                state = 32
            elif char == '=':
                state = 33
            elif char == ']':
                state = 34
            elif char == 'i':
                state = 35
            elif char == 'm':
                state = 36
            elif char == '}':
                state = 37
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
                state = 83
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
            if char == '.':
                state = 83
            elif '0' <= char <= '9':
                state = 5
                continue
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
                state = 82
            else:
                break
        if state == 7:
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 7
                return ~i
            if char == '=':
                state = 77
            elif char == '<':
                state = 78
            elif char == '>':
                state = 79
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
                state = 73
            elif char == '=':
                state = 74
            elif char == '/':
                state = 75
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
                state = 71
            else:
                break
        if state == 13:
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 13
                return ~i
            if '(' <= char <= '\xff':
                state = 13
                continue
            elif '\x00' <= char <= '&':
                state = 13
                continue
            elif char == "'":
                state = 29
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
                state = 67
            elif char == '\\':
                state = 68
            elif char == '/':
                state = 69
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
            if char == '=':
                state = 65
            elif char == '-':
                state = 66
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
                state = 29
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
                state = 29
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
                state = 64
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
                state = 63
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
                state = 62
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
            if char == '=':
                state = 60
            elif char == '>':
                state = 61
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
            if char == 'l':
                state = 56
            elif 'A' <= char <= 'Z':
                state = 10
                continue
            elif 'm' <= char <= 'z':
                state = 10
                continue
            elif 'a' <= char <= 'k':
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
        if state == 27:
            runner.last_matched_index = i - 1
            runner.last_matched_state = state
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 27
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
                state = 54
            else:
                break
        if state == 30:
            runner.last_matched_index = i - 1
            runner.last_matched_state = state
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 30
                return i
            if '\x0b' <= char <= '\xff':
                state = 30
                continue
            elif '\x00' <= char <= '\t':
                state = 30
                continue
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
            if char == '-':
                state = 51
            elif char == '>':
                state = 52
            else:
                break
        if state == 33:
            runner.last_matched_index = i - 1
            runner.last_matched_state = state
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 33
                return i
            if char == '@':
                state = 41
            elif char == '\\':
                state = 42
            elif char == '.':
                state = 43
            elif char == ':':
                state = 44
            elif char == '=':
                state = 45
            elif char == '<':
                state = 46
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
            if char == 's':
                state = 40
            elif 'A' <= char <= 'Z':
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
            else:
                break
        if state == 36:
            runner.last_matched_index = i - 1
            runner.last_matched_state = state
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 36
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
                state = 39
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
            runner.last_matched_index = i - 1
            runner.last_matched_state = state
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 40
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
        if state == 41:
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 41
                return ~i
            if char == '=':
                state = 50
            else:
                break
        if state == 42:
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 42
                return ~i
            if char == '=':
                state = 49
            else:
                break
        if state == 43:
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 43
                return ~i
            if char == '.':
                state = 48
            else:
                break
        if state == 44:
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 44
                return ~i
            if char == '=':
                state = 47
            else:
                break
        if state == 51:
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 51
                return ~i
            if char == '>':
                state = 53
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
                state = 55
            else:
                break
        if state == 55:
            runner.last_matched_index = i - 1
            runner.last_matched_state = state
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 55
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
        if state == 56:
            runner.last_matched_index = i - 1
            runner.last_matched_state = state
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 56
                return i
            if char == 'o':
                state = 57
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
        if state == 57:
            runner.last_matched_index = i - 1
            runner.last_matched_state = state
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 57
                return i
            if 'A' <= char <= 'Z':
                state = 10
                continue
            elif 'd' <= char <= 'z':
                state = 10
                continue
            elif '0' <= char <= '9':
                state = 10
                continue
            elif char == 'a':
                state = 10
                continue
            elif char == 'b':
                state = 10
                continue
            elif char == '_':
                state = 10
                continue
            elif char == 'c':
                state = 58
            else:
                break
        if state == 58:
            runner.last_matched_index = i - 1
            runner.last_matched_state = state
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 58
                return i
            if 'A' <= char <= 'Z':
                state = 10
                continue
            elif 'l' <= char <= 'z':
                state = 10
                continue
            elif '0' <= char <= '9':
                state = 10
                continue
            elif 'a' <= char <= 'j':
                state = 10
                continue
            elif char == '_':
                state = 10
                continue
            elif char == 'k':
                state = 59
            else:
                break
        if state == 59:
            runner.last_matched_index = i - 1
            runner.last_matched_state = state
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 59
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
        if state == 67:
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 67
                return ~i
            if '+' <= char <= '\xff':
                state = 67
                continue
            elif '\x00' <= char <= ')':
                state = 67
                continue
            elif char == '*':
                state = 70
            else:
                break
        if state == 70:
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 70
                return ~i
            if char == '/':
                state = 1
            elif '0' <= char <= '\xff':
                state = 67
                continue
            elif '\x00' <= char <= '.':
                state = 67
                continue
            else:
                break
        if state == 71:
            runner.last_matched_index = i - 1
            runner.last_matched_state = state
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 71
                return i
            if char == 'r':
                state = 72
            elif 'A' <= char <= 'Z':
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
            else:
                break
        if state == 72:
            runner.last_matched_index = i - 1
            runner.last_matched_state = state
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 72
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
        if state == 74:
            runner.last_matched_index = i - 1
            runner.last_matched_state = state
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 74
                return i
            if char == '=':
                state = 76
            else:
                break
        if state == 77:
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 77
                return ~i
            if char == '<':
                state = 81
            else:
                break
        if state == 79:
            runner.last_matched_index = i - 1
            runner.last_matched_state = state
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 79
                return i
            if char == '=':
                state = 80
            else:
                break
        if state == 83:
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 83
                return ~i
            if '0' <= char <= '9':
                state = 84
            else:
                break
        if state == 84:
            runner.last_matched_index = i - 1
            runner.last_matched_state = state
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 84
                return i
            if '0' <= char <= '9':
                state = 84
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
lexer = DummyLexer(recognize, DFA(85,
 {(0, '\t'): 1,
  (0, '\n'): 1,
  (0, ' '): 1,
  (0, '!'): 29,
  (0, '"'): 20,
  (0, '%'): 30,
  (0, "'"): 13,
  (0, '('): 2,
  (0, ')'): 31,
  (0, '*'): 21,
  (0, '+'): 14,
  (0, ','): 3,
  (0, '-'): 32,
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
  (0, '='): 33,
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
  (0, ']'): 34,
  (0, '^'): 25,
  (0, '_'): 8,
  (0, 'a'): 10,
  (0, 'b'): 26,
  (0, 'c'): 10,
  (0, 'd'): 10,
  (0, 'e'): 10,
  (0, 'f'): 10,
  (0, 'g'): 10,
  (0, 'h'): 10,
  (0, 'i'): 35,
  (0, 'j'): 10,
  (0, 'k'): 10,
  (0, 'l'): 10,
  (0, 'm'): 36,
  (0, 'n'): 10,
  (0, 'o'): 10,
  (0, 'p'): 10,
  (0, 'q'): 10,
  (0, 'r'): 27,
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
  (0, '}'): 37,
  (0, '~'): 28,
  (4, '.'): 83,
  (5, '.'): 83,
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
  (6, '<'): 82,
  (7, '<'): 78,
  (7, '='): 77,
  (7, '>'): 79,
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
  (9, '+'): 73,
  (9, '/'): 75,
  (9, '='): 74,
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
  (11, 'o'): 71,
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
  (13, "'"): 29,
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
  (15, '*'): 67,
  (15, '/'): 69,
  (15, '\\'): 68,
  (17, '-'): 66,
  (17, '='): 65,
  (18, ']'): 29,
  (19, '}'): 29,
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
  (20, '"'): 64,
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
  (21, '*'): 63,
  (23, '-'): 62,
  (24, '='): 60,
  (24, '>'): 61,
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
  (26, 'e'): 10,
  (26, 'f'): 10,
  (26, 'g'): 10,
  (26, 'h'): 10,
  (26, 'i'): 10,
  (26, 'j'): 10,
  (26, 'k'): 10,
  (26, 'l'): 56,
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
  (27, '0'): 10,
  (27, '1'): 10,
  (27, '2'): 10,
  (27, '3'): 10,
  (27, '4'): 10,
  (27, '5'): 10,
  (27, '6'): 10,
  (27, '7'): 10,
  (27, '8'): 10,
  (27, '9'): 10,
  (27, 'A'): 10,
  (27, 'B'): 10,
  (27, 'C'): 10,
  (27, 'D'): 10,
  (27, 'E'): 10,
  (27, 'F'): 10,
  (27, 'G'): 10,
  (27, 'H'): 10,
  (27, 'I'): 10,
  (27, 'J'): 10,
  (27, 'K'): 10,
  (27, 'L'): 10,
  (27, 'M'): 10,
  (27, 'N'): 10,
  (27, 'O'): 10,
  (27, 'P'): 10,
  (27, 'Q'): 10,
  (27, 'R'): 10,
  (27, 'S'): 10,
  (27, 'T'): 10,
  (27, 'U'): 10,
  (27, 'V'): 10,
  (27, 'W'): 10,
  (27, 'X'): 10,
  (27, 'Y'): 10,
  (27, 'Z'): 10,
  (27, '_'): 10,
  (27, 'a'): 10,
  (27, 'b'): 10,
  (27, 'c'): 10,
  (27, 'd'): 10,
  (27, 'e'): 54,
  (27, 'f'): 10,
  (27, 'g'): 10,
  (27, 'h'): 10,
  (27, 'i'): 10,
  (27, 'j'): 10,
  (27, 'k'): 10,
  (27, 'l'): 10,
  (27, 'm'): 10,
  (27, 'n'): 10,
  (27, 'o'): 10,
  (27, 'p'): 10,
  (27, 'q'): 10,
  (27, 'r'): 10,
  (27, 's'): 10,
  (27, 't'): 10,
  (27, 'u'): 10,
  (27, 'v'): 10,
  (27, 'w'): 10,
  (27, 'x'): 10,
  (27, 'y'): 10,
  (27, 'z'): 10,
  (30, '\x00'): 30,
  (30, '\x01'): 30,
  (30, '\x02'): 30,
  (30, '\x03'): 30,
  (30, '\x04'): 30,
  (30, '\x05'): 30,
  (30, '\x06'): 30,
  (30, '\x07'): 30,
  (30, '\x08'): 30,
  (30, '\t'): 30,
  (30, '\x0b'): 30,
  (30, '\x0c'): 30,
  (30, '\r'): 30,
  (30, '\x0e'): 30,
  (30, '\x0f'): 30,
  (30, '\x10'): 30,
  (30, '\x11'): 30,
  (30, '\x12'): 30,
  (30, '\x13'): 30,
  (30, '\x14'): 30,
  (30, '\x15'): 30,
  (30, '\x16'): 30,
  (30, '\x17'): 30,
  (30, '\x18'): 30,
  (30, '\x19'): 30,
  (30, '\x1a'): 30,
  (30, '\x1b'): 30,
  (30, '\x1c'): 30,
  (30, '\x1d'): 30,
  (30, '\x1e'): 30,
  (30, '\x1f'): 30,
  (30, ' '): 30,
  (30, '!'): 30,
  (30, '"'): 30,
  (30, '#'): 30,
  (30, '$'): 30,
  (30, '%'): 30,
  (30, '&'): 30,
  (30, "'"): 30,
  (30, '('): 30,
  (30, ')'): 30,
  (30, '*'): 30,
  (30, '+'): 30,
  (30, ','): 30,
  (30, '-'): 30,
  (30, '.'): 30,
  (30, '/'): 30,
  (30, '0'): 30,
  (30, '1'): 30,
  (30, '2'): 30,
  (30, '3'): 30,
  (30, '4'): 30,
  (30, '5'): 30,
  (30, '6'): 30,
  (30, '7'): 30,
  (30, '8'): 30,
  (30, '9'): 30,
  (30, ':'): 30,
  (30, ';'): 30,
  (30, '<'): 30,
  (30, '='): 30,
  (30, '>'): 30,
  (30, '?'): 30,
  (30, '@'): 30,
  (30, 'A'): 30,
  (30, 'B'): 30,
  (30, 'C'): 30,
  (30, 'D'): 30,
  (30, 'E'): 30,
  (30, 'F'): 30,
  (30, 'G'): 30,
  (30, 'H'): 30,
  (30, 'I'): 30,
  (30, 'J'): 30,
  (30, 'K'): 30,
  (30, 'L'): 30,
  (30, 'M'): 30,
  (30, 'N'): 30,
  (30, 'O'): 30,
  (30, 'P'): 30,
  (30, 'Q'): 30,
  (30, 'R'): 30,
  (30, 'S'): 30,
  (30, 'T'): 30,
  (30, 'U'): 30,
  (30, 'V'): 30,
  (30, 'W'): 30,
  (30, 'X'): 30,
  (30, 'Y'): 30,
  (30, 'Z'): 30,
  (30, '['): 30,
  (30, '\\'): 30,
  (30, ']'): 30,
  (30, '^'): 30,
  (30, '_'): 30,
  (30, '`'): 30,
  (30, 'a'): 30,
  (30, 'b'): 30,
  (30, 'c'): 30,
  (30, 'd'): 30,
  (30, 'e'): 30,
  (30, 'f'): 30,
  (30, 'g'): 30,
  (30, 'h'): 30,
  (30, 'i'): 30,
  (30, 'j'): 30,
  (30, 'k'): 30,
  (30, 'l'): 30,
  (30, 'm'): 30,
  (30, 'n'): 30,
  (30, 'o'): 30,
  (30, 'p'): 30,
  (30, 'q'): 30,
  (30, 'r'): 30,
  (30, 's'): 30,
  (30, 't'): 30,
  (30, 'u'): 30,
  (30, 'v'): 30,
  (30, 'w'): 30,
  (30, 'x'): 30,
  (30, 'y'): 30,
  (30, 'z'): 30,
  (30, '{'): 30,
  (30, '|'): 30,
  (30, '}'): 30,
  (30, '~'): 30,
  (30, '\x7f'): 30,
  (30, '\x80'): 30,
  (30, '\x81'): 30,
  (30, '\x82'): 30,
  (30, '\x83'): 30,
  (30, '\x84'): 30,
  (30, '\x85'): 30,
  (30, '\x86'): 30,
  (30, '\x87'): 30,
  (30, '\x88'): 30,
  (30, '\x89'): 30,
  (30, '\x8a'): 30,
  (30, '\x8b'): 30,
  (30, '\x8c'): 30,
  (30, '\x8d'): 30,
  (30, '\x8e'): 30,
  (30, '\x8f'): 30,
  (30, '\x90'): 30,
  (30, '\x91'): 30,
  (30, '\x92'): 30,
  (30, '\x93'): 30,
  (30, '\x94'): 30,
  (30, '\x95'): 30,
  (30, '\x96'): 30,
  (30, '\x97'): 30,
  (30, '\x98'): 30,
  (30, '\x99'): 30,
  (30, '\x9a'): 30,
  (30, '\x9b'): 30,
  (30, '\x9c'): 30,
  (30, '\x9d'): 30,
  (30, '\x9e'): 30,
  (30, '\x9f'): 30,
  (30, '\xa0'): 30,
  (30, '\xa1'): 30,
  (30, '\xa2'): 30,
  (30, '\xa3'): 30,
  (30, '\xa4'): 30,
  (30, '\xa5'): 30,
  (30, '\xa6'): 30,
  (30, '\xa7'): 30,
  (30, '\xa8'): 30,
  (30, '\xa9'): 30,
  (30, '\xaa'): 30,
  (30, '\xab'): 30,
  (30, '\xac'): 30,
  (30, '\xad'): 30,
  (30, '\xae'): 30,
  (30, '\xaf'): 30,
  (30, '\xb0'): 30,
  (30, '\xb1'): 30,
  (30, '\xb2'): 30,
  (30, '\xb3'): 30,
  (30, '\xb4'): 30,
  (30, '\xb5'): 30,
  (30, '\xb6'): 30,
  (30, '\xb7'): 30,
  (30, '\xb8'): 30,
  (30, '\xb9'): 30,
  (30, '\xba'): 30,
  (30, '\xbb'): 30,
  (30, '\xbc'): 30,
  (30, '\xbd'): 30,
  (30, '\xbe'): 30,
  (30, '\xbf'): 30,
  (30, '\xc0'): 30,
  (30, '\xc1'): 30,
  (30, '\xc2'): 30,
  (30, '\xc3'): 30,
  (30, '\xc4'): 30,
  (30, '\xc5'): 30,
  (30, '\xc6'): 30,
  (30, '\xc7'): 30,
  (30, '\xc8'): 30,
  (30, '\xc9'): 30,
  (30, '\xca'): 30,
  (30, '\xcb'): 30,
  (30, '\xcc'): 30,
  (30, '\xcd'): 30,
  (30, '\xce'): 30,
  (30, '\xcf'): 30,
  (30, '\xd0'): 30,
  (30, '\xd1'): 30,
  (30, '\xd2'): 30,
  (30, '\xd3'): 30,
  (30, '\xd4'): 30,
  (30, '\xd5'): 30,
  (30, '\xd6'): 30,
  (30, '\xd7'): 30,
  (30, '\xd8'): 30,
  (30, '\xd9'): 30,
  (30, '\xda'): 30,
  (30, '\xdb'): 30,
  (30, '\xdc'): 30,
  (30, '\xdd'): 30,
  (30, '\xde'): 30,
  (30, '\xdf'): 30,
  (30, '\xe0'): 30,
  (30, '\xe1'): 30,
  (30, '\xe2'): 30,
  (30, '\xe3'): 30,
  (30, '\xe4'): 30,
  (30, '\xe5'): 30,
  (30, '\xe6'): 30,
  (30, '\xe7'): 30,
  (30, '\xe8'): 30,
  (30, '\xe9'): 30,
  (30, '\xea'): 30,
  (30, '\xeb'): 30,
  (30, '\xec'): 30,
  (30, '\xed'): 30,
  (30, '\xee'): 30,
  (30, '\xef'): 30,
  (30, '\xf0'): 30,
  (30, '\xf1'): 30,
  (30, '\xf2'): 30,
  (30, '\xf3'): 30,
  (30, '\xf4'): 30,
  (30, '\xf5'): 30,
  (30, '\xf6'): 30,
  (30, '\xf7'): 30,
  (30, '\xf8'): 30,
  (30, '\xf9'): 30,
  (30, '\xfa'): 30,
  (30, '\xfb'): 30,
  (30, '\xfc'): 30,
  (30, '\xfd'): 30,
  (30, '\xfe'): 30,
  (30, '\xff'): 30,
  (32, '-'): 51,
  (32, '>'): 52,
  (33, '.'): 43,
  (33, ':'): 44,
  (33, '<'): 46,
  (33, '='): 45,
  (33, '@'): 41,
  (33, '\\'): 42,
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
  (35, 'o'): 10,
  (35, 'p'): 10,
  (35, 'q'): 10,
  (35, 'r'): 10,
  (35, 's'): 40,
  (35, 't'): 10,
  (35, 'u'): 10,
  (35, 'v'): 10,
  (35, 'w'): 10,
  (35, 'x'): 10,
  (35, 'y'): 10,
  (35, 'z'): 10,
  (36, '0'): 10,
  (36, '1'): 10,
  (36, '2'): 10,
  (36, '3'): 10,
  (36, '4'): 10,
  (36, '5'): 10,
  (36, '6'): 10,
  (36, '7'): 10,
  (36, '8'): 10,
  (36, '9'): 10,
  (36, 'A'): 10,
  (36, 'B'): 10,
  (36, 'C'): 10,
  (36, 'D'): 10,
  (36, 'E'): 10,
  (36, 'F'): 10,
  (36, 'G'): 10,
  (36, 'H'): 10,
  (36, 'I'): 10,
  (36, 'J'): 10,
  (36, 'K'): 10,
  (36, 'L'): 10,
  (36, 'M'): 10,
  (36, 'N'): 10,
  (36, 'O'): 10,
  (36, 'P'): 10,
  (36, 'Q'): 10,
  (36, 'R'): 10,
  (36, 'S'): 10,
  (36, 'T'): 10,
  (36, 'U'): 10,
  (36, 'V'): 10,
  (36, 'W'): 10,
  (36, 'X'): 10,
  (36, 'Y'): 10,
  (36, 'Z'): 10,
  (36, '_'): 10,
  (36, 'a'): 10,
  (36, 'b'): 10,
  (36, 'c'): 10,
  (36, 'd'): 10,
  (36, 'e'): 10,
  (36, 'f'): 10,
  (36, 'g'): 10,
  (36, 'h'): 10,
  (36, 'i'): 10,
  (36, 'j'): 10,
  (36, 'k'): 10,
  (36, 'l'): 10,
  (36, 'm'): 10,
  (36, 'n'): 10,
  (36, 'o'): 38,
  (36, 'p'): 10,
  (36, 'q'): 10,
  (36, 'r'): 10,
  (36, 's'): 10,
  (36, 't'): 10,
  (36, 'u'): 10,
  (36, 'v'): 10,
  (36, 'w'): 10,
  (36, 'x'): 10,
  (36, 'y'): 10,
  (36, 'z'): 10,
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
  (38, 'd'): 39,
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
  (40, '0'): 10,
  (40, '1'): 10,
  (40, '2'): 10,
  (40, '3'): 10,
  (40, '4'): 10,
  (40, '5'): 10,
  (40, '6'): 10,
  (40, '7'): 10,
  (40, '8'): 10,
  (40, '9'): 10,
  (40, 'A'): 10,
  (40, 'B'): 10,
  (40, 'C'): 10,
  (40, 'D'): 10,
  (40, 'E'): 10,
  (40, 'F'): 10,
  (40, 'G'): 10,
  (40, 'H'): 10,
  (40, 'I'): 10,
  (40, 'J'): 10,
  (40, 'K'): 10,
  (40, 'L'): 10,
  (40, 'M'): 10,
  (40, 'N'): 10,
  (40, 'O'): 10,
  (40, 'P'): 10,
  (40, 'Q'): 10,
  (40, 'R'): 10,
  (40, 'S'): 10,
  (40, 'T'): 10,
  (40, 'U'): 10,
  (40, 'V'): 10,
  (40, 'W'): 10,
  (40, 'X'): 10,
  (40, 'Y'): 10,
  (40, 'Z'): 10,
  (40, '_'): 10,
  (40, 'a'): 10,
  (40, 'b'): 10,
  (40, 'c'): 10,
  (40, 'd'): 10,
  (40, 'e'): 10,
  (40, 'f'): 10,
  (40, 'g'): 10,
  (40, 'h'): 10,
  (40, 'i'): 10,
  (40, 'j'): 10,
  (40, 'k'): 10,
  (40, 'l'): 10,
  (40, 'm'): 10,
  (40, 'n'): 10,
  (40, 'o'): 10,
  (40, 'p'): 10,
  (40, 'q'): 10,
  (40, 'r'): 10,
  (40, 's'): 10,
  (40, 't'): 10,
  (40, 'u'): 10,
  (40, 'v'): 10,
  (40, 'w'): 10,
  (40, 'x'): 10,
  (40, 'y'): 10,
  (40, 'z'): 10,
  (41, '='): 50,
  (42, '='): 49,
  (43, '.'): 48,
  (44, '='): 47,
  (51, '>'): 53,
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
  (54, 'm'): 55,
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
  (55, '0'): 10,
  (55, '1'): 10,
  (55, '2'): 10,
  (55, '3'): 10,
  (55, '4'): 10,
  (55, '5'): 10,
  (55, '6'): 10,
  (55, '7'): 10,
  (55, '8'): 10,
  (55, '9'): 10,
  (55, 'A'): 10,
  (55, 'B'): 10,
  (55, 'C'): 10,
  (55, 'D'): 10,
  (55, 'E'): 10,
  (55, 'F'): 10,
  (55, 'G'): 10,
  (55, 'H'): 10,
  (55, 'I'): 10,
  (55, 'J'): 10,
  (55, 'K'): 10,
  (55, 'L'): 10,
  (55, 'M'): 10,
  (55, 'N'): 10,
  (55, 'O'): 10,
  (55, 'P'): 10,
  (55, 'Q'): 10,
  (55, 'R'): 10,
  (55, 'S'): 10,
  (55, 'T'): 10,
  (55, 'U'): 10,
  (55, 'V'): 10,
  (55, 'W'): 10,
  (55, 'X'): 10,
  (55, 'Y'): 10,
  (55, 'Z'): 10,
  (55, '_'): 10,
  (55, 'a'): 10,
  (55, 'b'): 10,
  (55, 'c'): 10,
  (55, 'd'): 10,
  (55, 'e'): 10,
  (55, 'f'): 10,
  (55, 'g'): 10,
  (55, 'h'): 10,
  (55, 'i'): 10,
  (55, 'j'): 10,
  (55, 'k'): 10,
  (55, 'l'): 10,
  (55, 'm'): 10,
  (55, 'n'): 10,
  (55, 'o'): 10,
  (55, 'p'): 10,
  (55, 'q'): 10,
  (55, 'r'): 10,
  (55, 's'): 10,
  (55, 't'): 10,
  (55, 'u'): 10,
  (55, 'v'): 10,
  (55, 'w'): 10,
  (55, 'x'): 10,
  (55, 'y'): 10,
  (55, 'z'): 10,
  (56, '0'): 10,
  (56, '1'): 10,
  (56, '2'): 10,
  (56, '3'): 10,
  (56, '4'): 10,
  (56, '5'): 10,
  (56, '6'): 10,
  (56, '7'): 10,
  (56, '8'): 10,
  (56, '9'): 10,
  (56, 'A'): 10,
  (56, 'B'): 10,
  (56, 'C'): 10,
  (56, 'D'): 10,
  (56, 'E'): 10,
  (56, 'F'): 10,
  (56, 'G'): 10,
  (56, 'H'): 10,
  (56, 'I'): 10,
  (56, 'J'): 10,
  (56, 'K'): 10,
  (56, 'L'): 10,
  (56, 'M'): 10,
  (56, 'N'): 10,
  (56, 'O'): 10,
  (56, 'P'): 10,
  (56, 'Q'): 10,
  (56, 'R'): 10,
  (56, 'S'): 10,
  (56, 'T'): 10,
  (56, 'U'): 10,
  (56, 'V'): 10,
  (56, 'W'): 10,
  (56, 'X'): 10,
  (56, 'Y'): 10,
  (56, 'Z'): 10,
  (56, '_'): 10,
  (56, 'a'): 10,
  (56, 'b'): 10,
  (56, 'c'): 10,
  (56, 'd'): 10,
  (56, 'e'): 10,
  (56, 'f'): 10,
  (56, 'g'): 10,
  (56, 'h'): 10,
  (56, 'i'): 10,
  (56, 'j'): 10,
  (56, 'k'): 10,
  (56, 'l'): 10,
  (56, 'm'): 10,
  (56, 'n'): 10,
  (56, 'o'): 57,
  (56, 'p'): 10,
  (56, 'q'): 10,
  (56, 'r'): 10,
  (56, 's'): 10,
  (56, 't'): 10,
  (56, 'u'): 10,
  (56, 'v'): 10,
  (56, 'w'): 10,
  (56, 'x'): 10,
  (56, 'y'): 10,
  (56, 'z'): 10,
  (57, '0'): 10,
  (57, '1'): 10,
  (57, '2'): 10,
  (57, '3'): 10,
  (57, '4'): 10,
  (57, '5'): 10,
  (57, '6'): 10,
  (57, '7'): 10,
  (57, '8'): 10,
  (57, '9'): 10,
  (57, 'A'): 10,
  (57, 'B'): 10,
  (57, 'C'): 10,
  (57, 'D'): 10,
  (57, 'E'): 10,
  (57, 'F'): 10,
  (57, 'G'): 10,
  (57, 'H'): 10,
  (57, 'I'): 10,
  (57, 'J'): 10,
  (57, 'K'): 10,
  (57, 'L'): 10,
  (57, 'M'): 10,
  (57, 'N'): 10,
  (57, 'O'): 10,
  (57, 'P'): 10,
  (57, 'Q'): 10,
  (57, 'R'): 10,
  (57, 'S'): 10,
  (57, 'T'): 10,
  (57, 'U'): 10,
  (57, 'V'): 10,
  (57, 'W'): 10,
  (57, 'X'): 10,
  (57, 'Y'): 10,
  (57, 'Z'): 10,
  (57, '_'): 10,
  (57, 'a'): 10,
  (57, 'b'): 10,
  (57, 'c'): 58,
  (57, 'd'): 10,
  (57, 'e'): 10,
  (57, 'f'): 10,
  (57, 'g'): 10,
  (57, 'h'): 10,
  (57, 'i'): 10,
  (57, 'j'): 10,
  (57, 'k'): 10,
  (57, 'l'): 10,
  (57, 'm'): 10,
  (57, 'n'): 10,
  (57, 'o'): 10,
  (57, 'p'): 10,
  (57, 'q'): 10,
  (57, 'r'): 10,
  (57, 's'): 10,
  (57, 't'): 10,
  (57, 'u'): 10,
  (57, 'v'): 10,
  (57, 'w'): 10,
  (57, 'x'): 10,
  (57, 'y'): 10,
  (57, 'z'): 10,
  (58, '0'): 10,
  (58, '1'): 10,
  (58, '2'): 10,
  (58, '3'): 10,
  (58, '4'): 10,
  (58, '5'): 10,
  (58, '6'): 10,
  (58, '7'): 10,
  (58, '8'): 10,
  (58, '9'): 10,
  (58, 'A'): 10,
  (58, 'B'): 10,
  (58, 'C'): 10,
  (58, 'D'): 10,
  (58, 'E'): 10,
  (58, 'F'): 10,
  (58, 'G'): 10,
  (58, 'H'): 10,
  (58, 'I'): 10,
  (58, 'J'): 10,
  (58, 'K'): 10,
  (58, 'L'): 10,
  (58, 'M'): 10,
  (58, 'N'): 10,
  (58, 'O'): 10,
  (58, 'P'): 10,
  (58, 'Q'): 10,
  (58, 'R'): 10,
  (58, 'S'): 10,
  (58, 'T'): 10,
  (58, 'U'): 10,
  (58, 'V'): 10,
  (58, 'W'): 10,
  (58, 'X'): 10,
  (58, 'Y'): 10,
  (58, 'Z'): 10,
  (58, '_'): 10,
  (58, 'a'): 10,
  (58, 'b'): 10,
  (58, 'c'): 10,
  (58, 'd'): 10,
  (58, 'e'): 10,
  (58, 'f'): 10,
  (58, 'g'): 10,
  (58, 'h'): 10,
  (58, 'i'): 10,
  (58, 'j'): 10,
  (58, 'k'): 59,
  (58, 'l'): 10,
  (58, 'm'): 10,
  (58, 'n'): 10,
  (58, 'o'): 10,
  (58, 'p'): 10,
  (58, 'q'): 10,
  (58, 'r'): 10,
  (58, 's'): 10,
  (58, 't'): 10,
  (58, 'u'): 10,
  (58, 'v'): 10,
  (58, 'w'): 10,
  (58, 'x'): 10,
  (58, 'y'): 10,
  (58, 'z'): 10,
  (59, '0'): 10,
  (59, '1'): 10,
  (59, '2'): 10,
  (59, '3'): 10,
  (59, '4'): 10,
  (59, '5'): 10,
  (59, '6'): 10,
  (59, '7'): 10,
  (59, '8'): 10,
  (59, '9'): 10,
  (59, 'A'): 10,
  (59, 'B'): 10,
  (59, 'C'): 10,
  (59, 'D'): 10,
  (59, 'E'): 10,
  (59, 'F'): 10,
  (59, 'G'): 10,
  (59, 'H'): 10,
  (59, 'I'): 10,
  (59, 'J'): 10,
  (59, 'K'): 10,
  (59, 'L'): 10,
  (59, 'M'): 10,
  (59, 'N'): 10,
  (59, 'O'): 10,
  (59, 'P'): 10,
  (59, 'Q'): 10,
  (59, 'R'): 10,
  (59, 'S'): 10,
  (59, 'T'): 10,
  (59, 'U'): 10,
  (59, 'V'): 10,
  (59, 'W'): 10,
  (59, 'X'): 10,
  (59, 'Y'): 10,
  (59, 'Z'): 10,
  (59, '_'): 10,
  (59, 'a'): 10,
  (59, 'b'): 10,
  (59, 'c'): 10,
  (59, 'd'): 10,
  (59, 'e'): 10,
  (59, 'f'): 10,
  (59, 'g'): 10,
  (59, 'h'): 10,
  (59, 'i'): 10,
  (59, 'j'): 10,
  (59, 'k'): 10,
  (59, 'l'): 10,
  (59, 'm'): 10,
  (59, 'n'): 10,
  (59, 'o'): 10,
  (59, 'p'): 10,
  (59, 'q'): 10,
  (59, 'r'): 10,
  (59, 's'): 10,
  (59, 't'): 10,
  (59, 'u'): 10,
  (59, 'v'): 10,
  (59, 'w'): 10,
  (59, 'x'): 10,
  (59, 'y'): 10,
  (59, 'z'): 10,
  (67, '\x00'): 67,
  (67, '\x01'): 67,
  (67, '\x02'): 67,
  (67, '\x03'): 67,
  (67, '\x04'): 67,
  (67, '\x05'): 67,
  (67, '\x06'): 67,
  (67, '\x07'): 67,
  (67, '\x08'): 67,
  (67, '\t'): 67,
  (67, '\n'): 67,
  (67, '\x0b'): 67,
  (67, '\x0c'): 67,
  (67, '\r'): 67,
  (67, '\x0e'): 67,
  (67, '\x0f'): 67,
  (67, '\x10'): 67,
  (67, '\x11'): 67,
  (67, '\x12'): 67,
  (67, '\x13'): 67,
  (67, '\x14'): 67,
  (67, '\x15'): 67,
  (67, '\x16'): 67,
  (67, '\x17'): 67,
  (67, '\x18'): 67,
  (67, '\x19'): 67,
  (67, '\x1a'): 67,
  (67, '\x1b'): 67,
  (67, '\x1c'): 67,
  (67, '\x1d'): 67,
  (67, '\x1e'): 67,
  (67, '\x1f'): 67,
  (67, ' '): 67,
  (67, '!'): 67,
  (67, '"'): 67,
  (67, '#'): 67,
  (67, '$'): 67,
  (67, '%'): 67,
  (67, '&'): 67,
  (67, "'"): 67,
  (67, '('): 67,
  (67, ')'): 67,
  (67, '*'): 70,
  (67, '+'): 67,
  (67, ','): 67,
  (67, '-'): 67,
  (67, '.'): 67,
  (67, '/'): 67,
  (67, '0'): 67,
  (67, '1'): 67,
  (67, '2'): 67,
  (67, '3'): 67,
  (67, '4'): 67,
  (67, '5'): 67,
  (67, '6'): 67,
  (67, '7'): 67,
  (67, '8'): 67,
  (67, '9'): 67,
  (67, ':'): 67,
  (67, ';'): 67,
  (67, '<'): 67,
  (67, '='): 67,
  (67, '>'): 67,
  (67, '?'): 67,
  (67, '@'): 67,
  (67, 'A'): 67,
  (67, 'B'): 67,
  (67, 'C'): 67,
  (67, 'D'): 67,
  (67, 'E'): 67,
  (67, 'F'): 67,
  (67, 'G'): 67,
  (67, 'H'): 67,
  (67, 'I'): 67,
  (67, 'J'): 67,
  (67, 'K'): 67,
  (67, 'L'): 67,
  (67, 'M'): 67,
  (67, 'N'): 67,
  (67, 'O'): 67,
  (67, 'P'): 67,
  (67, 'Q'): 67,
  (67, 'R'): 67,
  (67, 'S'): 67,
  (67, 'T'): 67,
  (67, 'U'): 67,
  (67, 'V'): 67,
  (67, 'W'): 67,
  (67, 'X'): 67,
  (67, 'Y'): 67,
  (67, 'Z'): 67,
  (67, '['): 67,
  (67, '\\'): 67,
  (67, ']'): 67,
  (67, '^'): 67,
  (67, '_'): 67,
  (67, '`'): 67,
  (67, 'a'): 67,
  (67, 'b'): 67,
  (67, 'c'): 67,
  (67, 'd'): 67,
  (67, 'e'): 67,
  (67, 'f'): 67,
  (67, 'g'): 67,
  (67, 'h'): 67,
  (67, 'i'): 67,
  (67, 'j'): 67,
  (67, 'k'): 67,
  (67, 'l'): 67,
  (67, 'm'): 67,
  (67, 'n'): 67,
  (67, 'o'): 67,
  (67, 'p'): 67,
  (67, 'q'): 67,
  (67, 'r'): 67,
  (67, 's'): 67,
  (67, 't'): 67,
  (67, 'u'): 67,
  (67, 'v'): 67,
  (67, 'w'): 67,
  (67, 'x'): 67,
  (67, 'y'): 67,
  (67, 'z'): 67,
  (67, '{'): 67,
  (67, '|'): 67,
  (67, '}'): 67,
  (67, '~'): 67,
  (67, '\x7f'): 67,
  (67, '\x80'): 67,
  (67, '\x81'): 67,
  (67, '\x82'): 67,
  (67, '\x83'): 67,
  (67, '\x84'): 67,
  (67, '\x85'): 67,
  (67, '\x86'): 67,
  (67, '\x87'): 67,
  (67, '\x88'): 67,
  (67, '\x89'): 67,
  (67, '\x8a'): 67,
  (67, '\x8b'): 67,
  (67, '\x8c'): 67,
  (67, '\x8d'): 67,
  (67, '\x8e'): 67,
  (67, '\x8f'): 67,
  (67, '\x90'): 67,
  (67, '\x91'): 67,
  (67, '\x92'): 67,
  (67, '\x93'): 67,
  (67, '\x94'): 67,
  (67, '\x95'): 67,
  (67, '\x96'): 67,
  (67, '\x97'): 67,
  (67, '\x98'): 67,
  (67, '\x99'): 67,
  (67, '\x9a'): 67,
  (67, '\x9b'): 67,
  (67, '\x9c'): 67,
  (67, '\x9d'): 67,
  (67, '\x9e'): 67,
  (67, '\x9f'): 67,
  (67, '\xa0'): 67,
  (67, '\xa1'): 67,
  (67, '\xa2'): 67,
  (67, '\xa3'): 67,
  (67, '\xa4'): 67,
  (67, '\xa5'): 67,
  (67, '\xa6'): 67,
  (67, '\xa7'): 67,
  (67, '\xa8'): 67,
  (67, '\xa9'): 67,
  (67, '\xaa'): 67,
  (67, '\xab'): 67,
  (67, '\xac'): 67,
  (67, '\xad'): 67,
  (67, '\xae'): 67,
  (67, '\xaf'): 67,
  (67, '\xb0'): 67,
  (67, '\xb1'): 67,
  (67, '\xb2'): 67,
  (67, '\xb3'): 67,
  (67, '\xb4'): 67,
  (67, '\xb5'): 67,
  (67, '\xb6'): 67,
  (67, '\xb7'): 67,
  (67, '\xb8'): 67,
  (67, '\xb9'): 67,
  (67, '\xba'): 67,
  (67, '\xbb'): 67,
  (67, '\xbc'): 67,
  (67, '\xbd'): 67,
  (67, '\xbe'): 67,
  (67, '\xbf'): 67,
  (67, '\xc0'): 67,
  (67, '\xc1'): 67,
  (67, '\xc2'): 67,
  (67, '\xc3'): 67,
  (67, '\xc4'): 67,
  (67, '\xc5'): 67,
  (67, '\xc6'): 67,
  (67, '\xc7'): 67,
  (67, '\xc8'): 67,
  (67, '\xc9'): 67,
  (67, '\xca'): 67,
  (67, '\xcb'): 67,
  (67, '\xcc'): 67,
  (67, '\xcd'): 67,
  (67, '\xce'): 67,
  (67, '\xcf'): 67,
  (67, '\xd0'): 67,
  (67, '\xd1'): 67,
  (67, '\xd2'): 67,
  (67, '\xd3'): 67,
  (67, '\xd4'): 67,
  (67, '\xd5'): 67,
  (67, '\xd6'): 67,
  (67, '\xd7'): 67,
  (67, '\xd8'): 67,
  (67, '\xd9'): 67,
  (67, '\xda'): 67,
  (67, '\xdb'): 67,
  (67, '\xdc'): 67,
  (67, '\xdd'): 67,
  (67, '\xde'): 67,
  (67, '\xdf'): 67,
  (67, '\xe0'): 67,
  (67, '\xe1'): 67,
  (67, '\xe2'): 67,
  (67, '\xe3'): 67,
  (67, '\xe4'): 67,
  (67, '\xe5'): 67,
  (67, '\xe6'): 67,
  (67, '\xe7'): 67,
  (67, '\xe8'): 67,
  (67, '\xe9'): 67,
  (67, '\xea'): 67,
  (67, '\xeb'): 67,
  (67, '\xec'): 67,
  (67, '\xed'): 67,
  (67, '\xee'): 67,
  (67, '\xef'): 67,
  (67, '\xf0'): 67,
  (67, '\xf1'): 67,
  (67, '\xf2'): 67,
  (67, '\xf3'): 67,
  (67, '\xf4'): 67,
  (67, '\xf5'): 67,
  (67, '\xf6'): 67,
  (67, '\xf7'): 67,
  (67, '\xf8'): 67,
  (67, '\xf9'): 67,
  (67, '\xfa'): 67,
  (67, '\xfb'): 67,
  (67, '\xfc'): 67,
  (67, '\xfd'): 67,
  (67, '\xfe'): 67,
  (67, '\xff'): 67,
  (70, '\x00'): 67,
  (70, '\x01'): 67,
  (70, '\x02'): 67,
  (70, '\x03'): 67,
  (70, '\x04'): 67,
  (70, '\x05'): 67,
  (70, '\x06'): 67,
  (70, '\x07'): 67,
  (70, '\x08'): 67,
  (70, '\t'): 67,
  (70, '\n'): 67,
  (70, '\x0b'): 67,
  (70, '\x0c'): 67,
  (70, '\r'): 67,
  (70, '\x0e'): 67,
  (70, '\x0f'): 67,
  (70, '\x10'): 67,
  (70, '\x11'): 67,
  (70, '\x12'): 67,
  (70, '\x13'): 67,
  (70, '\x14'): 67,
  (70, '\x15'): 67,
  (70, '\x16'): 67,
  (70, '\x17'): 67,
  (70, '\x18'): 67,
  (70, '\x19'): 67,
  (70, '\x1a'): 67,
  (70, '\x1b'): 67,
  (70, '\x1c'): 67,
  (70, '\x1d'): 67,
  (70, '\x1e'): 67,
  (70, '\x1f'): 67,
  (70, ' '): 67,
  (70, '!'): 67,
  (70, '"'): 67,
  (70, '#'): 67,
  (70, '$'): 67,
  (70, '%'): 67,
  (70, '&'): 67,
  (70, "'"): 67,
  (70, '('): 67,
  (70, ')'): 67,
  (70, '*'): 67,
  (70, '+'): 67,
  (70, ','): 67,
  (70, '-'): 67,
  (70, '.'): 67,
  (70, '/'): 1,
  (70, '0'): 67,
  (70, '1'): 67,
  (70, '2'): 67,
  (70, '3'): 67,
  (70, '4'): 67,
  (70, '5'): 67,
  (70, '6'): 67,
  (70, '7'): 67,
  (70, '8'): 67,
  (70, '9'): 67,
  (70, ':'): 67,
  (70, ';'): 67,
  (70, '<'): 67,
  (70, '='): 67,
  (70, '>'): 67,
  (70, '?'): 67,
  (70, '@'): 67,
  (70, 'A'): 67,
  (70, 'B'): 67,
  (70, 'C'): 67,
  (70, 'D'): 67,
  (70, 'E'): 67,
  (70, 'F'): 67,
  (70, 'G'): 67,
  (70, 'H'): 67,
  (70, 'I'): 67,
  (70, 'J'): 67,
  (70, 'K'): 67,
  (70, 'L'): 67,
  (70, 'M'): 67,
  (70, 'N'): 67,
  (70, 'O'): 67,
  (70, 'P'): 67,
  (70, 'Q'): 67,
  (70, 'R'): 67,
  (70, 'S'): 67,
  (70, 'T'): 67,
  (70, 'U'): 67,
  (70, 'V'): 67,
  (70, 'W'): 67,
  (70, 'X'): 67,
  (70, 'Y'): 67,
  (70, 'Z'): 67,
  (70, '['): 67,
  (70, '\\'): 67,
  (70, ']'): 67,
  (70, '^'): 67,
  (70, '_'): 67,
  (70, '`'): 67,
  (70, 'a'): 67,
  (70, 'b'): 67,
  (70, 'c'): 67,
  (70, 'd'): 67,
  (70, 'e'): 67,
  (70, 'f'): 67,
  (70, 'g'): 67,
  (70, 'h'): 67,
  (70, 'i'): 67,
  (70, 'j'): 67,
  (70, 'k'): 67,
  (70, 'l'): 67,
  (70, 'm'): 67,
  (70, 'n'): 67,
  (70, 'o'): 67,
  (70, 'p'): 67,
  (70, 'q'): 67,
  (70, 'r'): 67,
  (70, 's'): 67,
  (70, 't'): 67,
  (70, 'u'): 67,
  (70, 'v'): 67,
  (70, 'w'): 67,
  (70, 'x'): 67,
  (70, 'y'): 67,
  (70, 'z'): 67,
  (70, '{'): 67,
  (70, '|'): 67,
  (70, '}'): 67,
  (70, '~'): 67,
  (70, '\x7f'): 67,
  (70, '\x80'): 67,
  (70, '\x81'): 67,
  (70, '\x82'): 67,
  (70, '\x83'): 67,
  (70, '\x84'): 67,
  (70, '\x85'): 67,
  (70, '\x86'): 67,
  (70, '\x87'): 67,
  (70, '\x88'): 67,
  (70, '\x89'): 67,
  (70, '\x8a'): 67,
  (70, '\x8b'): 67,
  (70, '\x8c'): 67,
  (70, '\x8d'): 67,
  (70, '\x8e'): 67,
  (70, '\x8f'): 67,
  (70, '\x90'): 67,
  (70, '\x91'): 67,
  (70, '\x92'): 67,
  (70, '\x93'): 67,
  (70, '\x94'): 67,
  (70, '\x95'): 67,
  (70, '\x96'): 67,
  (70, '\x97'): 67,
  (70, '\x98'): 67,
  (70, '\x99'): 67,
  (70, '\x9a'): 67,
  (70, '\x9b'): 67,
  (70, '\x9c'): 67,
  (70, '\x9d'): 67,
  (70, '\x9e'): 67,
  (70, '\x9f'): 67,
  (70, '\xa0'): 67,
  (70, '\xa1'): 67,
  (70, '\xa2'): 67,
  (70, '\xa3'): 67,
  (70, '\xa4'): 67,
  (70, '\xa5'): 67,
  (70, '\xa6'): 67,
  (70, '\xa7'): 67,
  (70, '\xa8'): 67,
  (70, '\xa9'): 67,
  (70, '\xaa'): 67,
  (70, '\xab'): 67,
  (70, '\xac'): 67,
  (70, '\xad'): 67,
  (70, '\xae'): 67,
  (70, '\xaf'): 67,
  (70, '\xb0'): 67,
  (70, '\xb1'): 67,
  (70, '\xb2'): 67,
  (70, '\xb3'): 67,
  (70, '\xb4'): 67,
  (70, '\xb5'): 67,
  (70, '\xb6'): 67,
  (70, '\xb7'): 67,
  (70, '\xb8'): 67,
  (70, '\xb9'): 67,
  (70, '\xba'): 67,
  (70, '\xbb'): 67,
  (70, '\xbc'): 67,
  (70, '\xbd'): 67,
  (70, '\xbe'): 67,
  (70, '\xbf'): 67,
  (70, '\xc0'): 67,
  (70, '\xc1'): 67,
  (70, '\xc2'): 67,
  (70, '\xc3'): 67,
  (70, '\xc4'): 67,
  (70, '\xc5'): 67,
  (70, '\xc6'): 67,
  (70, '\xc7'): 67,
  (70, '\xc8'): 67,
  (70, '\xc9'): 67,
  (70, '\xca'): 67,
  (70, '\xcb'): 67,
  (70, '\xcc'): 67,
  (70, '\xcd'): 67,
  (70, '\xce'): 67,
  (70, '\xcf'): 67,
  (70, '\xd0'): 67,
  (70, '\xd1'): 67,
  (70, '\xd2'): 67,
  (70, '\xd3'): 67,
  (70, '\xd4'): 67,
  (70, '\xd5'): 67,
  (70, '\xd6'): 67,
  (70, '\xd7'): 67,
  (70, '\xd8'): 67,
  (70, '\xd9'): 67,
  (70, '\xda'): 67,
  (70, '\xdb'): 67,
  (70, '\xdc'): 67,
  (70, '\xdd'): 67,
  (70, '\xde'): 67,
  (70, '\xdf'): 67,
  (70, '\xe0'): 67,
  (70, '\xe1'): 67,
  (70, '\xe2'): 67,
  (70, '\xe3'): 67,
  (70, '\xe4'): 67,
  (70, '\xe5'): 67,
  (70, '\xe6'): 67,
  (70, '\xe7'): 67,
  (70, '\xe8'): 67,
  (70, '\xe9'): 67,
  (70, '\xea'): 67,
  (70, '\xeb'): 67,
  (70, '\xec'): 67,
  (70, '\xed'): 67,
  (70, '\xee'): 67,
  (70, '\xef'): 67,
  (70, '\xf0'): 67,
  (70, '\xf1'): 67,
  (70, '\xf2'): 67,
  (70, '\xf3'): 67,
  (70, '\xf4'): 67,
  (70, '\xf5'): 67,
  (70, '\xf6'): 67,
  (70, '\xf7'): 67,
  (70, '\xf8'): 67,
  (70, '\xf9'): 67,
  (70, '\xfa'): 67,
  (70, '\xfb'): 67,
  (70, '\xfc'): 67,
  (70, '\xfd'): 67,
  (70, '\xfe'): 67,
  (70, '\xff'): 67,
  (71, '0'): 10,
  (71, '1'): 10,
  (71, '2'): 10,
  (71, '3'): 10,
  (71, '4'): 10,
  (71, '5'): 10,
  (71, '6'): 10,
  (71, '7'): 10,
  (71, '8'): 10,
  (71, '9'): 10,
  (71, 'A'): 10,
  (71, 'B'): 10,
  (71, 'C'): 10,
  (71, 'D'): 10,
  (71, 'E'): 10,
  (71, 'F'): 10,
  (71, 'G'): 10,
  (71, 'H'): 10,
  (71, 'I'): 10,
  (71, 'J'): 10,
  (71, 'K'): 10,
  (71, 'L'): 10,
  (71, 'M'): 10,
  (71, 'N'): 10,
  (71, 'O'): 10,
  (71, 'P'): 10,
  (71, 'Q'): 10,
  (71, 'R'): 10,
  (71, 'S'): 10,
  (71, 'T'): 10,
  (71, 'U'): 10,
  (71, 'V'): 10,
  (71, 'W'): 10,
  (71, 'X'): 10,
  (71, 'Y'): 10,
  (71, 'Z'): 10,
  (71, '_'): 10,
  (71, 'a'): 10,
  (71, 'b'): 10,
  (71, 'c'): 10,
  (71, 'd'): 10,
  (71, 'e'): 10,
  (71, 'f'): 10,
  (71, 'g'): 10,
  (71, 'h'): 10,
  (71, 'i'): 10,
  (71, 'j'): 10,
  (71, 'k'): 10,
  (71, 'l'): 10,
  (71, 'm'): 10,
  (71, 'n'): 10,
  (71, 'o'): 10,
  (71, 'p'): 10,
  (71, 'q'): 10,
  (71, 'r'): 72,
  (71, 's'): 10,
  (71, 't'): 10,
  (71, 'u'): 10,
  (71, 'v'): 10,
  (71, 'w'): 10,
  (71, 'x'): 10,
  (71, 'y'): 10,
  (71, 'z'): 10,
  (72, '0'): 10,
  (72, '1'): 10,
  (72, '2'): 10,
  (72, '3'): 10,
  (72, '4'): 10,
  (72, '5'): 10,
  (72, '6'): 10,
  (72, '7'): 10,
  (72, '8'): 10,
  (72, '9'): 10,
  (72, 'A'): 10,
  (72, 'B'): 10,
  (72, 'C'): 10,
  (72, 'D'): 10,
  (72, 'E'): 10,
  (72, 'F'): 10,
  (72, 'G'): 10,
  (72, 'H'): 10,
  (72, 'I'): 10,
  (72, 'J'): 10,
  (72, 'K'): 10,
  (72, 'L'): 10,
  (72, 'M'): 10,
  (72, 'N'): 10,
  (72, 'O'): 10,
  (72, 'P'): 10,
  (72, 'Q'): 10,
  (72, 'R'): 10,
  (72, 'S'): 10,
  (72, 'T'): 10,
  (72, 'U'): 10,
  (72, 'V'): 10,
  (72, 'W'): 10,
  (72, 'X'): 10,
  (72, 'Y'): 10,
  (72, 'Z'): 10,
  (72, '_'): 10,
  (72, 'a'): 10,
  (72, 'b'): 10,
  (72, 'c'): 10,
  (72, 'd'): 10,
  (72, 'e'): 10,
  (72, 'f'): 10,
  (72, 'g'): 10,
  (72, 'h'): 10,
  (72, 'i'): 10,
  (72, 'j'): 10,
  (72, 'k'): 10,
  (72, 'l'): 10,
  (72, 'm'): 10,
  (72, 'n'): 10,
  (72, 'o'): 10,
  (72, 'p'): 10,
  (72, 'q'): 10,
  (72, 'r'): 10,
  (72, 's'): 10,
  (72, 't'): 10,
  (72, 'u'): 10,
  (72, 'v'): 10,
  (72, 'w'): 10,
  (72, 'x'): 10,
  (72, 'y'): 10,
  (72, 'z'): 10,
  (74, '='): 76,
  (77, '<'): 81,
  (79, '='): 80,
  (83, '0'): 84,
  (83, '1'): 84,
  (83, '2'): 84,
  (83, '3'): 84,
  (83, '4'): 84,
  (83, '5'): 84,
  (83, '6'): 84,
  (83, '7'): 84,
  (83, '8'): 84,
  (83, '9'): 84,
  (84, '0'): 84,
  (84, '1'): 84,
  (84, '2'): 84,
  (84, '3'): 84,
  (84, '4'): 84,
  (84, '5'): 84,
  (84, '6'): 84,
  (84, '7'): 84,
  (84, '8'): 84,
  (84, '9'): 84},
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
      40,
      45,
      46,
      47,
      48,
      49,
      50,
      52,
      53,
      54,
      55,
      56,
      57,
      58,
      59,
      60,
      61,
      62,
      63,
      64,
      65,
      66,
      68,
      69,
      71,
      72,
      73,
      74,
      75,
      76,
      78,
      79,
      80,
      81,
      82,
      84]),
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
      40,
      45,
      46,
      47,
      48,
      49,
      50,
      52,
      53,
      54,
      55,
      56,
      57,
      58,
      59,
      60,
      61,
      62,
      63,
      64,
      65,
      66,
      68,
      69,
      71,
      72,
      73,
      74,
      75,
      76,
      78,
      79,
      80,
      81,
      82,
      84]),
 ['0, 0, 0, 0, start|, 0, start|, 0, 0, 0, 0, 0, start|, 0, 0, 0, 0, start|, 0, start|, 0, 0, start|, 0, 0, 0, 0, 0, 0, 0, start|, 0, start|, start|, 0, 0, start|, 0, start|, start|, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0',
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
  '2',
  '2',
  '2',
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
  'ATOM',
  'ATOM',
  'ATOM',
  'ATOM',
  'ATOM',
  'ATOM',
  'ATOM',
  'STRING',
  'ATOM',
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
