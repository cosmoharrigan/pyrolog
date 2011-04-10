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
         (1150, [("fx",  ["meta_predicate"])]),
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
  Rule('toplevel_op_expr', [['expr1150', '-->', 'expr1150', 'extratoplevel_op_expr'], ['expr1150', ':-', 'expr1150', 'extratoplevel_op_expr'], [':-', 'expr1150', 'extratoplevel_op_expr'], ['?-', 'expr1150', 'extratoplevel_op_expr'], ['expr1150', 'extratoplevel_op_expr']]),
  Rule('extraexpr1150', [[]]),
  Rule('expr1150', [['meta_predicate', 'expr1100', 'extraexpr1150'], ['expr1100', 'extraexpr1150']]),
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
  Rule('toplevel_op_expr', [['expr1150', '-->', 'expr1150', 'extratoplevel_op_expr'], ['expr1150', ':-', 'expr1150', 'extratoplevel_op_expr'], [':-', 'expr1150', 'extratoplevel_op_expr'], ['?-', 'expr1150', 'extratoplevel_op_expr'], ['expr1150', 'extratoplevel_op_expr']]),
  Rule('extraexpr1150', [[]]),
  Rule('expr1150', [['meta_predicate', 'expr1100', 'extraexpr1150'], ['expr1100', 'extraexpr1150']]),
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
                state = 90
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
                state = 90
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
                state = 89
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
                state = 84
            elif char == '<':
                state = 85
            elif char == '>':
                state = 86
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
                state = 80
            elif char == '=':
                state = 81
            elif char == '/':
                state = 82
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
                state = 78
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
                state = 74
            elif char == '\\':
                state = 75
            elif char == '/':
                state = 76
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
                state = 73
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
                state = 72
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
                state = 71
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
                state = 70
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
                state = 68
            elif char == '>':
                state = 69
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
                state = 66
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
            if char == '>':
                state = 64
            elif char == '-':
                state = 63
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
                state = 53
            elif char == '<':
                state = 54
            elif char == '.':
                state = 55
            elif char == ':':
                state = 56
            elif char == '=':
                state = 57
            elif char == '\\':
                state = 58
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
                state = 52
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
            elif 'p' <= char <= 'z':
                state = 10
                continue
            elif '0' <= char <= '9':
                state = 10
                continue
            elif 'f' <= char <= 'n':
                state = 10
                continue
            elif 'a' <= char <= 'd':
                state = 10
                continue
            elif char == '_':
                state = 10
                continue
            elif char == 'e':
                state = 37
            elif char == 'o':
                state = 38
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
            if char == 't':
                state = 40
            elif 'A' <= char <= 'Z':
                state = 10
                continue
            elif 'a' <= char <= 's':
                state = 10
                continue
            elif '0' <= char <= '9':
                state = 10
                continue
            elif 'u' <= char <= 'z':
                state = 10
                continue
            elif char == '_':
                state = 10
                continue
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
            if char == 'a':
                state = 41
            elif 'A' <= char <= 'Z':
                state = 10
                continue
            elif 'b' <= char <= 'z':
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
            runner.last_matched_index = i - 1
            runner.last_matched_state = state
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 41
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
                state = 42
            else:
                break
        if state == 42:
            runner.last_matched_index = i - 1
            runner.last_matched_state = state
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 42
                return i
            if 'A' <= char <= 'Z':
                state = 10
                continue
            elif 'a' <= char <= 'o':
                state = 10
                continue
            elif '0' <= char <= '9':
                state = 10
                continue
            elif 'q' <= char <= 'z':
                state = 10
                continue
            elif char == '_':
                state = 10
                continue
            elif char == 'p':
                state = 43
            else:
                break
        if state == 43:
            runner.last_matched_index = i - 1
            runner.last_matched_state = state
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 43
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
                state = 44
            else:
                break
        if state == 44:
            runner.last_matched_index = i - 1
            runner.last_matched_state = state
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 44
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
                state = 45
            else:
                break
        if state == 45:
            runner.last_matched_index = i - 1
            runner.last_matched_state = state
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 45
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
                state = 46
            else:
                break
        if state == 46:
            runner.last_matched_index = i - 1
            runner.last_matched_state = state
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 46
                return i
            if 'A' <= char <= 'Z':
                state = 10
                continue
            elif 'j' <= char <= 'z':
                state = 10
                continue
            elif '0' <= char <= '9':
                state = 10
                continue
            elif 'a' <= char <= 'h':
                state = 10
                continue
            elif char == '_':
                state = 10
                continue
            elif char == 'i':
                state = 47
            else:
                break
        if state == 47:
            runner.last_matched_index = i - 1
            runner.last_matched_state = state
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 47
                return i
            if char == 'c':
                state = 48
            elif 'A' <= char <= 'Z':
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
            else:
                break
        if state == 48:
            runner.last_matched_index = i - 1
            runner.last_matched_state = state
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 48
                return i
            if char == 'a':
                state = 49
            elif 'A' <= char <= 'Z':
                state = 10
                continue
            elif 'b' <= char <= 'z':
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
        if state == 49:
            runner.last_matched_index = i - 1
            runner.last_matched_state = state
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 49
                return i
            if 'A' <= char <= 'Z':
                state = 10
                continue
            elif 'a' <= char <= 's':
                state = 10
                continue
            elif '0' <= char <= '9':
                state = 10
                continue
            elif 'u' <= char <= 'z':
                state = 10
                continue
            elif char == '_':
                state = 10
                continue
            elif char == 't':
                state = 50
            else:
                break
        if state == 50:
            runner.last_matched_index = i - 1
            runner.last_matched_state = state
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 50
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
                state = 51
            else:
                break
        if state == 51:
            runner.last_matched_index = i - 1
            runner.last_matched_state = state
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 51
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
        if state == 52:
            runner.last_matched_index = i - 1
            runner.last_matched_state = state
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 52
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
        if state == 53:
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 53
                return ~i
            if char == '=':
                state = 62
            else:
                break
        if state == 55:
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 55
                return ~i
            if char == '.':
                state = 61
            else:
                break
        if state == 56:
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 56
                return ~i
            if char == '=':
                state = 60
            else:
                break
        if state == 58:
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 58
                return ~i
            if char == '=':
                state = 59
            else:
                break
        if state == 63:
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 63
                return ~i
            if char == '>':
                state = 65
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
                state = 67
            else:
                break
        if state == 67:
            runner.last_matched_index = i - 1
            runner.last_matched_state = state
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 67
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
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 74
                return ~i
            if '+' <= char <= '\xff':
                state = 74
                continue
            elif '\x00' <= char <= ')':
                state = 74
                continue
            elif char == '*':
                state = 77
            else:
                break
        if state == 77:
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 77
                return ~i
            if char == '/':
                state = 1
            elif '0' <= char <= '\xff':
                state = 74
                continue
            elif '\x00' <= char <= '.':
                state = 74
                continue
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
                state = 79
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
        if state == 81:
            runner.last_matched_index = i - 1
            runner.last_matched_state = state
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 81
                return i
            if char == '=':
                state = 83
            else:
                break
        if state == 84:
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 84
                return ~i
            if char == '<':
                state = 88
            else:
                break
        if state == 86:
            runner.last_matched_index = i - 1
            runner.last_matched_state = state
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 86
                return i
            if char == '=':
                state = 87
            else:
                break
        if state == 90:
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 90
                return ~i
            if '0' <= char <= '9':
                state = 91
            else:
                break
        if state == 91:
            runner.last_matched_index = i - 1
            runner.last_matched_state = state
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 91
                return i
            if '0' <= char <= '9':
                state = 91
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
lexer = DummyLexer(recognize, DFA(92,
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
  (4, '.'): 90,
  (5, '.'): 90,
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
  (6, '<'): 89,
  (7, '<'): 85,
  (7, '='): 84,
  (7, '>'): 86,
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
  (9, '+'): 80,
  (9, '/'): 82,
  (9, '='): 81,
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
  (11, 'o'): 78,
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
  (15, '*'): 74,
  (15, '/'): 76,
  (15, '\\'): 75,
  (17, '-'): 73,
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
  (20, '"'): 72,
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
  (21, '*'): 71,
  (23, '-'): 70,
  (24, '='): 68,
  (24, '>'): 69,
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
  (26, 'e'): 66,
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
  (31, '-'): 63,
  (31, '>'): 64,
  (32, '.'): 55,
  (32, ':'): 56,
  (32, '<'): 54,
  (32, '='): 57,
  (32, '@'): 53,
  (32, '\\'): 58,
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
  (34, 's'): 52,
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
  (35, 'e'): 37,
  (35, 'f'): 10,
  (35, 'g'): 10,
  (35, 'h'): 10,
  (35, 'i'): 10,
  (35, 'j'): 10,
  (35, 'k'): 10,
  (35, 'l'): 10,
  (35, 'm'): 10,
  (35, 'n'): 10,
  (35, 'o'): 38,
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
  (37, 'd'): 10,
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
  (37, 't'): 40,
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
  (40, 'a'): 41,
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
  (41, '0'): 10,
  (41, '1'): 10,
  (41, '2'): 10,
  (41, '3'): 10,
  (41, '4'): 10,
  (41, '5'): 10,
  (41, '6'): 10,
  (41, '7'): 10,
  (41, '8'): 10,
  (41, '9'): 10,
  (41, 'A'): 10,
  (41, 'B'): 10,
  (41, 'C'): 10,
  (41, 'D'): 10,
  (41, 'E'): 10,
  (41, 'F'): 10,
  (41, 'G'): 10,
  (41, 'H'): 10,
  (41, 'I'): 10,
  (41, 'J'): 10,
  (41, 'K'): 10,
  (41, 'L'): 10,
  (41, 'M'): 10,
  (41, 'N'): 10,
  (41, 'O'): 10,
  (41, 'P'): 10,
  (41, 'Q'): 10,
  (41, 'R'): 10,
  (41, 'S'): 10,
  (41, 'T'): 10,
  (41, 'U'): 10,
  (41, 'V'): 10,
  (41, 'W'): 10,
  (41, 'X'): 10,
  (41, 'Y'): 10,
  (41, 'Z'): 10,
  (41, '_'): 42,
  (41, 'a'): 10,
  (41, 'b'): 10,
  (41, 'c'): 10,
  (41, 'd'): 10,
  (41, 'e'): 10,
  (41, 'f'): 10,
  (41, 'g'): 10,
  (41, 'h'): 10,
  (41, 'i'): 10,
  (41, 'j'): 10,
  (41, 'k'): 10,
  (41, 'l'): 10,
  (41, 'm'): 10,
  (41, 'n'): 10,
  (41, 'o'): 10,
  (41, 'p'): 10,
  (41, 'q'): 10,
  (41, 'r'): 10,
  (41, 's'): 10,
  (41, 't'): 10,
  (41, 'u'): 10,
  (41, 'v'): 10,
  (41, 'w'): 10,
  (41, 'x'): 10,
  (41, 'y'): 10,
  (41, 'z'): 10,
  (42, '0'): 10,
  (42, '1'): 10,
  (42, '2'): 10,
  (42, '3'): 10,
  (42, '4'): 10,
  (42, '5'): 10,
  (42, '6'): 10,
  (42, '7'): 10,
  (42, '8'): 10,
  (42, '9'): 10,
  (42, 'A'): 10,
  (42, 'B'): 10,
  (42, 'C'): 10,
  (42, 'D'): 10,
  (42, 'E'): 10,
  (42, 'F'): 10,
  (42, 'G'): 10,
  (42, 'H'): 10,
  (42, 'I'): 10,
  (42, 'J'): 10,
  (42, 'K'): 10,
  (42, 'L'): 10,
  (42, 'M'): 10,
  (42, 'N'): 10,
  (42, 'O'): 10,
  (42, 'P'): 10,
  (42, 'Q'): 10,
  (42, 'R'): 10,
  (42, 'S'): 10,
  (42, 'T'): 10,
  (42, 'U'): 10,
  (42, 'V'): 10,
  (42, 'W'): 10,
  (42, 'X'): 10,
  (42, 'Y'): 10,
  (42, 'Z'): 10,
  (42, '_'): 10,
  (42, 'a'): 10,
  (42, 'b'): 10,
  (42, 'c'): 10,
  (42, 'd'): 10,
  (42, 'e'): 10,
  (42, 'f'): 10,
  (42, 'g'): 10,
  (42, 'h'): 10,
  (42, 'i'): 10,
  (42, 'j'): 10,
  (42, 'k'): 10,
  (42, 'l'): 10,
  (42, 'm'): 10,
  (42, 'n'): 10,
  (42, 'o'): 10,
  (42, 'p'): 43,
  (42, 'q'): 10,
  (42, 'r'): 10,
  (42, 's'): 10,
  (42, 't'): 10,
  (42, 'u'): 10,
  (42, 'v'): 10,
  (42, 'w'): 10,
  (42, 'x'): 10,
  (42, 'y'): 10,
  (42, 'z'): 10,
  (43, '0'): 10,
  (43, '1'): 10,
  (43, '2'): 10,
  (43, '3'): 10,
  (43, '4'): 10,
  (43, '5'): 10,
  (43, '6'): 10,
  (43, '7'): 10,
  (43, '8'): 10,
  (43, '9'): 10,
  (43, 'A'): 10,
  (43, 'B'): 10,
  (43, 'C'): 10,
  (43, 'D'): 10,
  (43, 'E'): 10,
  (43, 'F'): 10,
  (43, 'G'): 10,
  (43, 'H'): 10,
  (43, 'I'): 10,
  (43, 'J'): 10,
  (43, 'K'): 10,
  (43, 'L'): 10,
  (43, 'M'): 10,
  (43, 'N'): 10,
  (43, 'O'): 10,
  (43, 'P'): 10,
  (43, 'Q'): 10,
  (43, 'R'): 10,
  (43, 'S'): 10,
  (43, 'T'): 10,
  (43, 'U'): 10,
  (43, 'V'): 10,
  (43, 'W'): 10,
  (43, 'X'): 10,
  (43, 'Y'): 10,
  (43, 'Z'): 10,
  (43, '_'): 10,
  (43, 'a'): 10,
  (43, 'b'): 10,
  (43, 'c'): 10,
  (43, 'd'): 10,
  (43, 'e'): 10,
  (43, 'f'): 10,
  (43, 'g'): 10,
  (43, 'h'): 10,
  (43, 'i'): 10,
  (43, 'j'): 10,
  (43, 'k'): 10,
  (43, 'l'): 10,
  (43, 'm'): 10,
  (43, 'n'): 10,
  (43, 'o'): 10,
  (43, 'p'): 10,
  (43, 'q'): 10,
  (43, 'r'): 44,
  (43, 's'): 10,
  (43, 't'): 10,
  (43, 'u'): 10,
  (43, 'v'): 10,
  (43, 'w'): 10,
  (43, 'x'): 10,
  (43, 'y'): 10,
  (43, 'z'): 10,
  (44, '0'): 10,
  (44, '1'): 10,
  (44, '2'): 10,
  (44, '3'): 10,
  (44, '4'): 10,
  (44, '5'): 10,
  (44, '6'): 10,
  (44, '7'): 10,
  (44, '8'): 10,
  (44, '9'): 10,
  (44, 'A'): 10,
  (44, 'B'): 10,
  (44, 'C'): 10,
  (44, 'D'): 10,
  (44, 'E'): 10,
  (44, 'F'): 10,
  (44, 'G'): 10,
  (44, 'H'): 10,
  (44, 'I'): 10,
  (44, 'J'): 10,
  (44, 'K'): 10,
  (44, 'L'): 10,
  (44, 'M'): 10,
  (44, 'N'): 10,
  (44, 'O'): 10,
  (44, 'P'): 10,
  (44, 'Q'): 10,
  (44, 'R'): 10,
  (44, 'S'): 10,
  (44, 'T'): 10,
  (44, 'U'): 10,
  (44, 'V'): 10,
  (44, 'W'): 10,
  (44, 'X'): 10,
  (44, 'Y'): 10,
  (44, 'Z'): 10,
  (44, '_'): 10,
  (44, 'a'): 10,
  (44, 'b'): 10,
  (44, 'c'): 10,
  (44, 'd'): 10,
  (44, 'e'): 45,
  (44, 'f'): 10,
  (44, 'g'): 10,
  (44, 'h'): 10,
  (44, 'i'): 10,
  (44, 'j'): 10,
  (44, 'k'): 10,
  (44, 'l'): 10,
  (44, 'm'): 10,
  (44, 'n'): 10,
  (44, 'o'): 10,
  (44, 'p'): 10,
  (44, 'q'): 10,
  (44, 'r'): 10,
  (44, 's'): 10,
  (44, 't'): 10,
  (44, 'u'): 10,
  (44, 'v'): 10,
  (44, 'w'): 10,
  (44, 'x'): 10,
  (44, 'y'): 10,
  (44, 'z'): 10,
  (45, '0'): 10,
  (45, '1'): 10,
  (45, '2'): 10,
  (45, '3'): 10,
  (45, '4'): 10,
  (45, '5'): 10,
  (45, '6'): 10,
  (45, '7'): 10,
  (45, '8'): 10,
  (45, '9'): 10,
  (45, 'A'): 10,
  (45, 'B'): 10,
  (45, 'C'): 10,
  (45, 'D'): 10,
  (45, 'E'): 10,
  (45, 'F'): 10,
  (45, 'G'): 10,
  (45, 'H'): 10,
  (45, 'I'): 10,
  (45, 'J'): 10,
  (45, 'K'): 10,
  (45, 'L'): 10,
  (45, 'M'): 10,
  (45, 'N'): 10,
  (45, 'O'): 10,
  (45, 'P'): 10,
  (45, 'Q'): 10,
  (45, 'R'): 10,
  (45, 'S'): 10,
  (45, 'T'): 10,
  (45, 'U'): 10,
  (45, 'V'): 10,
  (45, 'W'): 10,
  (45, 'X'): 10,
  (45, 'Y'): 10,
  (45, 'Z'): 10,
  (45, '_'): 10,
  (45, 'a'): 10,
  (45, 'b'): 10,
  (45, 'c'): 10,
  (45, 'd'): 46,
  (45, 'e'): 10,
  (45, 'f'): 10,
  (45, 'g'): 10,
  (45, 'h'): 10,
  (45, 'i'): 10,
  (45, 'j'): 10,
  (45, 'k'): 10,
  (45, 'l'): 10,
  (45, 'm'): 10,
  (45, 'n'): 10,
  (45, 'o'): 10,
  (45, 'p'): 10,
  (45, 'q'): 10,
  (45, 'r'): 10,
  (45, 's'): 10,
  (45, 't'): 10,
  (45, 'u'): 10,
  (45, 'v'): 10,
  (45, 'w'): 10,
  (45, 'x'): 10,
  (45, 'y'): 10,
  (45, 'z'): 10,
  (46, '0'): 10,
  (46, '1'): 10,
  (46, '2'): 10,
  (46, '3'): 10,
  (46, '4'): 10,
  (46, '5'): 10,
  (46, '6'): 10,
  (46, '7'): 10,
  (46, '8'): 10,
  (46, '9'): 10,
  (46, 'A'): 10,
  (46, 'B'): 10,
  (46, 'C'): 10,
  (46, 'D'): 10,
  (46, 'E'): 10,
  (46, 'F'): 10,
  (46, 'G'): 10,
  (46, 'H'): 10,
  (46, 'I'): 10,
  (46, 'J'): 10,
  (46, 'K'): 10,
  (46, 'L'): 10,
  (46, 'M'): 10,
  (46, 'N'): 10,
  (46, 'O'): 10,
  (46, 'P'): 10,
  (46, 'Q'): 10,
  (46, 'R'): 10,
  (46, 'S'): 10,
  (46, 'T'): 10,
  (46, 'U'): 10,
  (46, 'V'): 10,
  (46, 'W'): 10,
  (46, 'X'): 10,
  (46, 'Y'): 10,
  (46, 'Z'): 10,
  (46, '_'): 10,
  (46, 'a'): 10,
  (46, 'b'): 10,
  (46, 'c'): 10,
  (46, 'd'): 10,
  (46, 'e'): 10,
  (46, 'f'): 10,
  (46, 'g'): 10,
  (46, 'h'): 10,
  (46, 'i'): 47,
  (46, 'j'): 10,
  (46, 'k'): 10,
  (46, 'l'): 10,
  (46, 'm'): 10,
  (46, 'n'): 10,
  (46, 'o'): 10,
  (46, 'p'): 10,
  (46, 'q'): 10,
  (46, 'r'): 10,
  (46, 's'): 10,
  (46, 't'): 10,
  (46, 'u'): 10,
  (46, 'v'): 10,
  (46, 'w'): 10,
  (46, 'x'): 10,
  (46, 'y'): 10,
  (46, 'z'): 10,
  (47, '0'): 10,
  (47, '1'): 10,
  (47, '2'): 10,
  (47, '3'): 10,
  (47, '4'): 10,
  (47, '5'): 10,
  (47, '6'): 10,
  (47, '7'): 10,
  (47, '8'): 10,
  (47, '9'): 10,
  (47, 'A'): 10,
  (47, 'B'): 10,
  (47, 'C'): 10,
  (47, 'D'): 10,
  (47, 'E'): 10,
  (47, 'F'): 10,
  (47, 'G'): 10,
  (47, 'H'): 10,
  (47, 'I'): 10,
  (47, 'J'): 10,
  (47, 'K'): 10,
  (47, 'L'): 10,
  (47, 'M'): 10,
  (47, 'N'): 10,
  (47, 'O'): 10,
  (47, 'P'): 10,
  (47, 'Q'): 10,
  (47, 'R'): 10,
  (47, 'S'): 10,
  (47, 'T'): 10,
  (47, 'U'): 10,
  (47, 'V'): 10,
  (47, 'W'): 10,
  (47, 'X'): 10,
  (47, 'Y'): 10,
  (47, 'Z'): 10,
  (47, '_'): 10,
  (47, 'a'): 10,
  (47, 'b'): 10,
  (47, 'c'): 48,
  (47, 'd'): 10,
  (47, 'e'): 10,
  (47, 'f'): 10,
  (47, 'g'): 10,
  (47, 'h'): 10,
  (47, 'i'): 10,
  (47, 'j'): 10,
  (47, 'k'): 10,
  (47, 'l'): 10,
  (47, 'm'): 10,
  (47, 'n'): 10,
  (47, 'o'): 10,
  (47, 'p'): 10,
  (47, 'q'): 10,
  (47, 'r'): 10,
  (47, 's'): 10,
  (47, 't'): 10,
  (47, 'u'): 10,
  (47, 'v'): 10,
  (47, 'w'): 10,
  (47, 'x'): 10,
  (47, 'y'): 10,
  (47, 'z'): 10,
  (48, '0'): 10,
  (48, '1'): 10,
  (48, '2'): 10,
  (48, '3'): 10,
  (48, '4'): 10,
  (48, '5'): 10,
  (48, '6'): 10,
  (48, '7'): 10,
  (48, '8'): 10,
  (48, '9'): 10,
  (48, 'A'): 10,
  (48, 'B'): 10,
  (48, 'C'): 10,
  (48, 'D'): 10,
  (48, 'E'): 10,
  (48, 'F'): 10,
  (48, 'G'): 10,
  (48, 'H'): 10,
  (48, 'I'): 10,
  (48, 'J'): 10,
  (48, 'K'): 10,
  (48, 'L'): 10,
  (48, 'M'): 10,
  (48, 'N'): 10,
  (48, 'O'): 10,
  (48, 'P'): 10,
  (48, 'Q'): 10,
  (48, 'R'): 10,
  (48, 'S'): 10,
  (48, 'T'): 10,
  (48, 'U'): 10,
  (48, 'V'): 10,
  (48, 'W'): 10,
  (48, 'X'): 10,
  (48, 'Y'): 10,
  (48, 'Z'): 10,
  (48, '_'): 10,
  (48, 'a'): 49,
  (48, 'b'): 10,
  (48, 'c'): 10,
  (48, 'd'): 10,
  (48, 'e'): 10,
  (48, 'f'): 10,
  (48, 'g'): 10,
  (48, 'h'): 10,
  (48, 'i'): 10,
  (48, 'j'): 10,
  (48, 'k'): 10,
  (48, 'l'): 10,
  (48, 'm'): 10,
  (48, 'n'): 10,
  (48, 'o'): 10,
  (48, 'p'): 10,
  (48, 'q'): 10,
  (48, 'r'): 10,
  (48, 's'): 10,
  (48, 't'): 10,
  (48, 'u'): 10,
  (48, 'v'): 10,
  (48, 'w'): 10,
  (48, 'x'): 10,
  (48, 'y'): 10,
  (48, 'z'): 10,
  (49, '0'): 10,
  (49, '1'): 10,
  (49, '2'): 10,
  (49, '3'): 10,
  (49, '4'): 10,
  (49, '5'): 10,
  (49, '6'): 10,
  (49, '7'): 10,
  (49, '8'): 10,
  (49, '9'): 10,
  (49, 'A'): 10,
  (49, 'B'): 10,
  (49, 'C'): 10,
  (49, 'D'): 10,
  (49, 'E'): 10,
  (49, 'F'): 10,
  (49, 'G'): 10,
  (49, 'H'): 10,
  (49, 'I'): 10,
  (49, 'J'): 10,
  (49, 'K'): 10,
  (49, 'L'): 10,
  (49, 'M'): 10,
  (49, 'N'): 10,
  (49, 'O'): 10,
  (49, 'P'): 10,
  (49, 'Q'): 10,
  (49, 'R'): 10,
  (49, 'S'): 10,
  (49, 'T'): 10,
  (49, 'U'): 10,
  (49, 'V'): 10,
  (49, 'W'): 10,
  (49, 'X'): 10,
  (49, 'Y'): 10,
  (49, 'Z'): 10,
  (49, '_'): 10,
  (49, 'a'): 10,
  (49, 'b'): 10,
  (49, 'c'): 10,
  (49, 'd'): 10,
  (49, 'e'): 10,
  (49, 'f'): 10,
  (49, 'g'): 10,
  (49, 'h'): 10,
  (49, 'i'): 10,
  (49, 'j'): 10,
  (49, 'k'): 10,
  (49, 'l'): 10,
  (49, 'm'): 10,
  (49, 'n'): 10,
  (49, 'o'): 10,
  (49, 'p'): 10,
  (49, 'q'): 10,
  (49, 'r'): 10,
  (49, 's'): 10,
  (49, 't'): 50,
  (49, 'u'): 10,
  (49, 'v'): 10,
  (49, 'w'): 10,
  (49, 'x'): 10,
  (49, 'y'): 10,
  (49, 'z'): 10,
  (50, '0'): 10,
  (50, '1'): 10,
  (50, '2'): 10,
  (50, '3'): 10,
  (50, '4'): 10,
  (50, '5'): 10,
  (50, '6'): 10,
  (50, '7'): 10,
  (50, '8'): 10,
  (50, '9'): 10,
  (50, 'A'): 10,
  (50, 'B'): 10,
  (50, 'C'): 10,
  (50, 'D'): 10,
  (50, 'E'): 10,
  (50, 'F'): 10,
  (50, 'G'): 10,
  (50, 'H'): 10,
  (50, 'I'): 10,
  (50, 'J'): 10,
  (50, 'K'): 10,
  (50, 'L'): 10,
  (50, 'M'): 10,
  (50, 'N'): 10,
  (50, 'O'): 10,
  (50, 'P'): 10,
  (50, 'Q'): 10,
  (50, 'R'): 10,
  (50, 'S'): 10,
  (50, 'T'): 10,
  (50, 'U'): 10,
  (50, 'V'): 10,
  (50, 'W'): 10,
  (50, 'X'): 10,
  (50, 'Y'): 10,
  (50, 'Z'): 10,
  (50, '_'): 10,
  (50, 'a'): 10,
  (50, 'b'): 10,
  (50, 'c'): 10,
  (50, 'd'): 10,
  (50, 'e'): 51,
  (50, 'f'): 10,
  (50, 'g'): 10,
  (50, 'h'): 10,
  (50, 'i'): 10,
  (50, 'j'): 10,
  (50, 'k'): 10,
  (50, 'l'): 10,
  (50, 'm'): 10,
  (50, 'n'): 10,
  (50, 'o'): 10,
  (50, 'p'): 10,
  (50, 'q'): 10,
  (50, 'r'): 10,
  (50, 's'): 10,
  (50, 't'): 10,
  (50, 'u'): 10,
  (50, 'v'): 10,
  (50, 'w'): 10,
  (50, 'x'): 10,
  (50, 'y'): 10,
  (50, 'z'): 10,
  (51, '0'): 10,
  (51, '1'): 10,
  (51, '2'): 10,
  (51, '3'): 10,
  (51, '4'): 10,
  (51, '5'): 10,
  (51, '6'): 10,
  (51, '7'): 10,
  (51, '8'): 10,
  (51, '9'): 10,
  (51, 'A'): 10,
  (51, 'B'): 10,
  (51, 'C'): 10,
  (51, 'D'): 10,
  (51, 'E'): 10,
  (51, 'F'): 10,
  (51, 'G'): 10,
  (51, 'H'): 10,
  (51, 'I'): 10,
  (51, 'J'): 10,
  (51, 'K'): 10,
  (51, 'L'): 10,
  (51, 'M'): 10,
  (51, 'N'): 10,
  (51, 'O'): 10,
  (51, 'P'): 10,
  (51, 'Q'): 10,
  (51, 'R'): 10,
  (51, 'S'): 10,
  (51, 'T'): 10,
  (51, 'U'): 10,
  (51, 'V'): 10,
  (51, 'W'): 10,
  (51, 'X'): 10,
  (51, 'Y'): 10,
  (51, 'Z'): 10,
  (51, '_'): 10,
  (51, 'a'): 10,
  (51, 'b'): 10,
  (51, 'c'): 10,
  (51, 'd'): 10,
  (51, 'e'): 10,
  (51, 'f'): 10,
  (51, 'g'): 10,
  (51, 'h'): 10,
  (51, 'i'): 10,
  (51, 'j'): 10,
  (51, 'k'): 10,
  (51, 'l'): 10,
  (51, 'm'): 10,
  (51, 'n'): 10,
  (51, 'o'): 10,
  (51, 'p'): 10,
  (51, 'q'): 10,
  (51, 'r'): 10,
  (51, 's'): 10,
  (51, 't'): 10,
  (51, 'u'): 10,
  (51, 'v'): 10,
  (51, 'w'): 10,
  (51, 'x'): 10,
  (51, 'y'): 10,
  (51, 'z'): 10,
  (52, '0'): 10,
  (52, '1'): 10,
  (52, '2'): 10,
  (52, '3'): 10,
  (52, '4'): 10,
  (52, '5'): 10,
  (52, '6'): 10,
  (52, '7'): 10,
  (52, '8'): 10,
  (52, '9'): 10,
  (52, 'A'): 10,
  (52, 'B'): 10,
  (52, 'C'): 10,
  (52, 'D'): 10,
  (52, 'E'): 10,
  (52, 'F'): 10,
  (52, 'G'): 10,
  (52, 'H'): 10,
  (52, 'I'): 10,
  (52, 'J'): 10,
  (52, 'K'): 10,
  (52, 'L'): 10,
  (52, 'M'): 10,
  (52, 'N'): 10,
  (52, 'O'): 10,
  (52, 'P'): 10,
  (52, 'Q'): 10,
  (52, 'R'): 10,
  (52, 'S'): 10,
  (52, 'T'): 10,
  (52, 'U'): 10,
  (52, 'V'): 10,
  (52, 'W'): 10,
  (52, 'X'): 10,
  (52, 'Y'): 10,
  (52, 'Z'): 10,
  (52, '_'): 10,
  (52, 'a'): 10,
  (52, 'b'): 10,
  (52, 'c'): 10,
  (52, 'd'): 10,
  (52, 'e'): 10,
  (52, 'f'): 10,
  (52, 'g'): 10,
  (52, 'h'): 10,
  (52, 'i'): 10,
  (52, 'j'): 10,
  (52, 'k'): 10,
  (52, 'l'): 10,
  (52, 'm'): 10,
  (52, 'n'): 10,
  (52, 'o'): 10,
  (52, 'p'): 10,
  (52, 'q'): 10,
  (52, 'r'): 10,
  (52, 's'): 10,
  (52, 't'): 10,
  (52, 'u'): 10,
  (52, 'v'): 10,
  (52, 'w'): 10,
  (52, 'x'): 10,
  (52, 'y'): 10,
  (52, 'z'): 10,
  (53, '='): 62,
  (55, '.'): 61,
  (56, '='): 60,
  (58, '='): 59,
  (63, '>'): 65,
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
  (66, 'm'): 67,
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
  (67, '0'): 10,
  (67, '1'): 10,
  (67, '2'): 10,
  (67, '3'): 10,
  (67, '4'): 10,
  (67, '5'): 10,
  (67, '6'): 10,
  (67, '7'): 10,
  (67, '8'): 10,
  (67, '9'): 10,
  (67, 'A'): 10,
  (67, 'B'): 10,
  (67, 'C'): 10,
  (67, 'D'): 10,
  (67, 'E'): 10,
  (67, 'F'): 10,
  (67, 'G'): 10,
  (67, 'H'): 10,
  (67, 'I'): 10,
  (67, 'J'): 10,
  (67, 'K'): 10,
  (67, 'L'): 10,
  (67, 'M'): 10,
  (67, 'N'): 10,
  (67, 'O'): 10,
  (67, 'P'): 10,
  (67, 'Q'): 10,
  (67, 'R'): 10,
  (67, 'S'): 10,
  (67, 'T'): 10,
  (67, 'U'): 10,
  (67, 'V'): 10,
  (67, 'W'): 10,
  (67, 'X'): 10,
  (67, 'Y'): 10,
  (67, 'Z'): 10,
  (67, '_'): 10,
  (67, 'a'): 10,
  (67, 'b'): 10,
  (67, 'c'): 10,
  (67, 'd'): 10,
  (67, 'e'): 10,
  (67, 'f'): 10,
  (67, 'g'): 10,
  (67, 'h'): 10,
  (67, 'i'): 10,
  (67, 'j'): 10,
  (67, 'k'): 10,
  (67, 'l'): 10,
  (67, 'm'): 10,
  (67, 'n'): 10,
  (67, 'o'): 10,
  (67, 'p'): 10,
  (67, 'q'): 10,
  (67, 'r'): 10,
  (67, 's'): 10,
  (67, 't'): 10,
  (67, 'u'): 10,
  (67, 'v'): 10,
  (67, 'w'): 10,
  (67, 'x'): 10,
  (67, 'y'): 10,
  (67, 'z'): 10,
  (74, '\x00'): 74,
  (74, '\x01'): 74,
  (74, '\x02'): 74,
  (74, '\x03'): 74,
  (74, '\x04'): 74,
  (74, '\x05'): 74,
  (74, '\x06'): 74,
  (74, '\x07'): 74,
  (74, '\x08'): 74,
  (74, '\t'): 74,
  (74, '\n'): 74,
  (74, '\x0b'): 74,
  (74, '\x0c'): 74,
  (74, '\r'): 74,
  (74, '\x0e'): 74,
  (74, '\x0f'): 74,
  (74, '\x10'): 74,
  (74, '\x11'): 74,
  (74, '\x12'): 74,
  (74, '\x13'): 74,
  (74, '\x14'): 74,
  (74, '\x15'): 74,
  (74, '\x16'): 74,
  (74, '\x17'): 74,
  (74, '\x18'): 74,
  (74, '\x19'): 74,
  (74, '\x1a'): 74,
  (74, '\x1b'): 74,
  (74, '\x1c'): 74,
  (74, '\x1d'): 74,
  (74, '\x1e'): 74,
  (74, '\x1f'): 74,
  (74, ' '): 74,
  (74, '!'): 74,
  (74, '"'): 74,
  (74, '#'): 74,
  (74, '$'): 74,
  (74, '%'): 74,
  (74, '&'): 74,
  (74, "'"): 74,
  (74, '('): 74,
  (74, ')'): 74,
  (74, '*'): 77,
  (74, '+'): 74,
  (74, ','): 74,
  (74, '-'): 74,
  (74, '.'): 74,
  (74, '/'): 74,
  (74, '0'): 74,
  (74, '1'): 74,
  (74, '2'): 74,
  (74, '3'): 74,
  (74, '4'): 74,
  (74, '5'): 74,
  (74, '6'): 74,
  (74, '7'): 74,
  (74, '8'): 74,
  (74, '9'): 74,
  (74, ':'): 74,
  (74, ';'): 74,
  (74, '<'): 74,
  (74, '='): 74,
  (74, '>'): 74,
  (74, '?'): 74,
  (74, '@'): 74,
  (74, 'A'): 74,
  (74, 'B'): 74,
  (74, 'C'): 74,
  (74, 'D'): 74,
  (74, 'E'): 74,
  (74, 'F'): 74,
  (74, 'G'): 74,
  (74, 'H'): 74,
  (74, 'I'): 74,
  (74, 'J'): 74,
  (74, 'K'): 74,
  (74, 'L'): 74,
  (74, 'M'): 74,
  (74, 'N'): 74,
  (74, 'O'): 74,
  (74, 'P'): 74,
  (74, 'Q'): 74,
  (74, 'R'): 74,
  (74, 'S'): 74,
  (74, 'T'): 74,
  (74, 'U'): 74,
  (74, 'V'): 74,
  (74, 'W'): 74,
  (74, 'X'): 74,
  (74, 'Y'): 74,
  (74, 'Z'): 74,
  (74, '['): 74,
  (74, '\\'): 74,
  (74, ']'): 74,
  (74, '^'): 74,
  (74, '_'): 74,
  (74, '`'): 74,
  (74, 'a'): 74,
  (74, 'b'): 74,
  (74, 'c'): 74,
  (74, 'd'): 74,
  (74, 'e'): 74,
  (74, 'f'): 74,
  (74, 'g'): 74,
  (74, 'h'): 74,
  (74, 'i'): 74,
  (74, 'j'): 74,
  (74, 'k'): 74,
  (74, 'l'): 74,
  (74, 'm'): 74,
  (74, 'n'): 74,
  (74, 'o'): 74,
  (74, 'p'): 74,
  (74, 'q'): 74,
  (74, 'r'): 74,
  (74, 's'): 74,
  (74, 't'): 74,
  (74, 'u'): 74,
  (74, 'v'): 74,
  (74, 'w'): 74,
  (74, 'x'): 74,
  (74, 'y'): 74,
  (74, 'z'): 74,
  (74, '{'): 74,
  (74, '|'): 74,
  (74, '}'): 74,
  (74, '~'): 74,
  (74, '\x7f'): 74,
  (74, '\x80'): 74,
  (74, '\x81'): 74,
  (74, '\x82'): 74,
  (74, '\x83'): 74,
  (74, '\x84'): 74,
  (74, '\x85'): 74,
  (74, '\x86'): 74,
  (74, '\x87'): 74,
  (74, '\x88'): 74,
  (74, '\x89'): 74,
  (74, '\x8a'): 74,
  (74, '\x8b'): 74,
  (74, '\x8c'): 74,
  (74, '\x8d'): 74,
  (74, '\x8e'): 74,
  (74, '\x8f'): 74,
  (74, '\x90'): 74,
  (74, '\x91'): 74,
  (74, '\x92'): 74,
  (74, '\x93'): 74,
  (74, '\x94'): 74,
  (74, '\x95'): 74,
  (74, '\x96'): 74,
  (74, '\x97'): 74,
  (74, '\x98'): 74,
  (74, '\x99'): 74,
  (74, '\x9a'): 74,
  (74, '\x9b'): 74,
  (74, '\x9c'): 74,
  (74, '\x9d'): 74,
  (74, '\x9e'): 74,
  (74, '\x9f'): 74,
  (74, '\xa0'): 74,
  (74, '\xa1'): 74,
  (74, '\xa2'): 74,
  (74, '\xa3'): 74,
  (74, '\xa4'): 74,
  (74, '\xa5'): 74,
  (74, '\xa6'): 74,
  (74, '\xa7'): 74,
  (74, '\xa8'): 74,
  (74, '\xa9'): 74,
  (74, '\xaa'): 74,
  (74, '\xab'): 74,
  (74, '\xac'): 74,
  (74, '\xad'): 74,
  (74, '\xae'): 74,
  (74, '\xaf'): 74,
  (74, '\xb0'): 74,
  (74, '\xb1'): 74,
  (74, '\xb2'): 74,
  (74, '\xb3'): 74,
  (74, '\xb4'): 74,
  (74, '\xb5'): 74,
  (74, '\xb6'): 74,
  (74, '\xb7'): 74,
  (74, '\xb8'): 74,
  (74, '\xb9'): 74,
  (74, '\xba'): 74,
  (74, '\xbb'): 74,
  (74, '\xbc'): 74,
  (74, '\xbd'): 74,
  (74, '\xbe'): 74,
  (74, '\xbf'): 74,
  (74, '\xc0'): 74,
  (74, '\xc1'): 74,
  (74, '\xc2'): 74,
  (74, '\xc3'): 74,
  (74, '\xc4'): 74,
  (74, '\xc5'): 74,
  (74, '\xc6'): 74,
  (74, '\xc7'): 74,
  (74, '\xc8'): 74,
  (74, '\xc9'): 74,
  (74, '\xca'): 74,
  (74, '\xcb'): 74,
  (74, '\xcc'): 74,
  (74, '\xcd'): 74,
  (74, '\xce'): 74,
  (74, '\xcf'): 74,
  (74, '\xd0'): 74,
  (74, '\xd1'): 74,
  (74, '\xd2'): 74,
  (74, '\xd3'): 74,
  (74, '\xd4'): 74,
  (74, '\xd5'): 74,
  (74, '\xd6'): 74,
  (74, '\xd7'): 74,
  (74, '\xd8'): 74,
  (74, '\xd9'): 74,
  (74, '\xda'): 74,
  (74, '\xdb'): 74,
  (74, '\xdc'): 74,
  (74, '\xdd'): 74,
  (74, '\xde'): 74,
  (74, '\xdf'): 74,
  (74, '\xe0'): 74,
  (74, '\xe1'): 74,
  (74, '\xe2'): 74,
  (74, '\xe3'): 74,
  (74, '\xe4'): 74,
  (74, '\xe5'): 74,
  (74, '\xe6'): 74,
  (74, '\xe7'): 74,
  (74, '\xe8'): 74,
  (74, '\xe9'): 74,
  (74, '\xea'): 74,
  (74, '\xeb'): 74,
  (74, '\xec'): 74,
  (74, '\xed'): 74,
  (74, '\xee'): 74,
  (74, '\xef'): 74,
  (74, '\xf0'): 74,
  (74, '\xf1'): 74,
  (74, '\xf2'): 74,
  (74, '\xf3'): 74,
  (74, '\xf4'): 74,
  (74, '\xf5'): 74,
  (74, '\xf6'): 74,
  (74, '\xf7'): 74,
  (74, '\xf8'): 74,
  (74, '\xf9'): 74,
  (74, '\xfa'): 74,
  (74, '\xfb'): 74,
  (74, '\xfc'): 74,
  (74, '\xfd'): 74,
  (74, '\xfe'): 74,
  (74, '\xff'): 74,
  (77, '\x00'): 74,
  (77, '\x01'): 74,
  (77, '\x02'): 74,
  (77, '\x03'): 74,
  (77, '\x04'): 74,
  (77, '\x05'): 74,
  (77, '\x06'): 74,
  (77, '\x07'): 74,
  (77, '\x08'): 74,
  (77, '\t'): 74,
  (77, '\n'): 74,
  (77, '\x0b'): 74,
  (77, '\x0c'): 74,
  (77, '\r'): 74,
  (77, '\x0e'): 74,
  (77, '\x0f'): 74,
  (77, '\x10'): 74,
  (77, '\x11'): 74,
  (77, '\x12'): 74,
  (77, '\x13'): 74,
  (77, '\x14'): 74,
  (77, '\x15'): 74,
  (77, '\x16'): 74,
  (77, '\x17'): 74,
  (77, '\x18'): 74,
  (77, '\x19'): 74,
  (77, '\x1a'): 74,
  (77, '\x1b'): 74,
  (77, '\x1c'): 74,
  (77, '\x1d'): 74,
  (77, '\x1e'): 74,
  (77, '\x1f'): 74,
  (77, ' '): 74,
  (77, '!'): 74,
  (77, '"'): 74,
  (77, '#'): 74,
  (77, '$'): 74,
  (77, '%'): 74,
  (77, '&'): 74,
  (77, "'"): 74,
  (77, '('): 74,
  (77, ')'): 74,
  (77, '*'): 74,
  (77, '+'): 74,
  (77, ','): 74,
  (77, '-'): 74,
  (77, '.'): 74,
  (77, '/'): 1,
  (77, '0'): 74,
  (77, '1'): 74,
  (77, '2'): 74,
  (77, '3'): 74,
  (77, '4'): 74,
  (77, '5'): 74,
  (77, '6'): 74,
  (77, '7'): 74,
  (77, '8'): 74,
  (77, '9'): 74,
  (77, ':'): 74,
  (77, ';'): 74,
  (77, '<'): 74,
  (77, '='): 74,
  (77, '>'): 74,
  (77, '?'): 74,
  (77, '@'): 74,
  (77, 'A'): 74,
  (77, 'B'): 74,
  (77, 'C'): 74,
  (77, 'D'): 74,
  (77, 'E'): 74,
  (77, 'F'): 74,
  (77, 'G'): 74,
  (77, 'H'): 74,
  (77, 'I'): 74,
  (77, 'J'): 74,
  (77, 'K'): 74,
  (77, 'L'): 74,
  (77, 'M'): 74,
  (77, 'N'): 74,
  (77, 'O'): 74,
  (77, 'P'): 74,
  (77, 'Q'): 74,
  (77, 'R'): 74,
  (77, 'S'): 74,
  (77, 'T'): 74,
  (77, 'U'): 74,
  (77, 'V'): 74,
  (77, 'W'): 74,
  (77, 'X'): 74,
  (77, 'Y'): 74,
  (77, 'Z'): 74,
  (77, '['): 74,
  (77, '\\'): 74,
  (77, ']'): 74,
  (77, '^'): 74,
  (77, '_'): 74,
  (77, '`'): 74,
  (77, 'a'): 74,
  (77, 'b'): 74,
  (77, 'c'): 74,
  (77, 'd'): 74,
  (77, 'e'): 74,
  (77, 'f'): 74,
  (77, 'g'): 74,
  (77, 'h'): 74,
  (77, 'i'): 74,
  (77, 'j'): 74,
  (77, 'k'): 74,
  (77, 'l'): 74,
  (77, 'm'): 74,
  (77, 'n'): 74,
  (77, 'o'): 74,
  (77, 'p'): 74,
  (77, 'q'): 74,
  (77, 'r'): 74,
  (77, 's'): 74,
  (77, 't'): 74,
  (77, 'u'): 74,
  (77, 'v'): 74,
  (77, 'w'): 74,
  (77, 'x'): 74,
  (77, 'y'): 74,
  (77, 'z'): 74,
  (77, '{'): 74,
  (77, '|'): 74,
  (77, '}'): 74,
  (77, '~'): 74,
  (77, '\x7f'): 74,
  (77, '\x80'): 74,
  (77, '\x81'): 74,
  (77, '\x82'): 74,
  (77, '\x83'): 74,
  (77, '\x84'): 74,
  (77, '\x85'): 74,
  (77, '\x86'): 74,
  (77, '\x87'): 74,
  (77, '\x88'): 74,
  (77, '\x89'): 74,
  (77, '\x8a'): 74,
  (77, '\x8b'): 74,
  (77, '\x8c'): 74,
  (77, '\x8d'): 74,
  (77, '\x8e'): 74,
  (77, '\x8f'): 74,
  (77, '\x90'): 74,
  (77, '\x91'): 74,
  (77, '\x92'): 74,
  (77, '\x93'): 74,
  (77, '\x94'): 74,
  (77, '\x95'): 74,
  (77, '\x96'): 74,
  (77, '\x97'): 74,
  (77, '\x98'): 74,
  (77, '\x99'): 74,
  (77, '\x9a'): 74,
  (77, '\x9b'): 74,
  (77, '\x9c'): 74,
  (77, '\x9d'): 74,
  (77, '\x9e'): 74,
  (77, '\x9f'): 74,
  (77, '\xa0'): 74,
  (77, '\xa1'): 74,
  (77, '\xa2'): 74,
  (77, '\xa3'): 74,
  (77, '\xa4'): 74,
  (77, '\xa5'): 74,
  (77, '\xa6'): 74,
  (77, '\xa7'): 74,
  (77, '\xa8'): 74,
  (77, '\xa9'): 74,
  (77, '\xaa'): 74,
  (77, '\xab'): 74,
  (77, '\xac'): 74,
  (77, '\xad'): 74,
  (77, '\xae'): 74,
  (77, '\xaf'): 74,
  (77, '\xb0'): 74,
  (77, '\xb1'): 74,
  (77, '\xb2'): 74,
  (77, '\xb3'): 74,
  (77, '\xb4'): 74,
  (77, '\xb5'): 74,
  (77, '\xb6'): 74,
  (77, '\xb7'): 74,
  (77, '\xb8'): 74,
  (77, '\xb9'): 74,
  (77, '\xba'): 74,
  (77, '\xbb'): 74,
  (77, '\xbc'): 74,
  (77, '\xbd'): 74,
  (77, '\xbe'): 74,
  (77, '\xbf'): 74,
  (77, '\xc0'): 74,
  (77, '\xc1'): 74,
  (77, '\xc2'): 74,
  (77, '\xc3'): 74,
  (77, '\xc4'): 74,
  (77, '\xc5'): 74,
  (77, '\xc6'): 74,
  (77, '\xc7'): 74,
  (77, '\xc8'): 74,
  (77, '\xc9'): 74,
  (77, '\xca'): 74,
  (77, '\xcb'): 74,
  (77, '\xcc'): 74,
  (77, '\xcd'): 74,
  (77, '\xce'): 74,
  (77, '\xcf'): 74,
  (77, '\xd0'): 74,
  (77, '\xd1'): 74,
  (77, '\xd2'): 74,
  (77, '\xd3'): 74,
  (77, '\xd4'): 74,
  (77, '\xd5'): 74,
  (77, '\xd6'): 74,
  (77, '\xd7'): 74,
  (77, '\xd8'): 74,
  (77, '\xd9'): 74,
  (77, '\xda'): 74,
  (77, '\xdb'): 74,
  (77, '\xdc'): 74,
  (77, '\xdd'): 74,
  (77, '\xde'): 74,
  (77, '\xdf'): 74,
  (77, '\xe0'): 74,
  (77, '\xe1'): 74,
  (77, '\xe2'): 74,
  (77, '\xe3'): 74,
  (77, '\xe4'): 74,
  (77, '\xe5'): 74,
  (77, '\xe6'): 74,
  (77, '\xe7'): 74,
  (77, '\xe8'): 74,
  (77, '\xe9'): 74,
  (77, '\xea'): 74,
  (77, '\xeb'): 74,
  (77, '\xec'): 74,
  (77, '\xed'): 74,
  (77, '\xee'): 74,
  (77, '\xef'): 74,
  (77, '\xf0'): 74,
  (77, '\xf1'): 74,
  (77, '\xf2'): 74,
  (77, '\xf3'): 74,
  (77, '\xf4'): 74,
  (77, '\xf5'): 74,
  (77, '\xf6'): 74,
  (77, '\xf7'): 74,
  (77, '\xf8'): 74,
  (77, '\xf9'): 74,
  (77, '\xfa'): 74,
  (77, '\xfb'): 74,
  (77, '\xfc'): 74,
  (77, '\xfd'): 74,
  (77, '\xfe'): 74,
  (77, '\xff'): 74,
  (78, '0'): 10,
  (78, '1'): 10,
  (78, '2'): 10,
  (78, '3'): 10,
  (78, '4'): 10,
  (78, '5'): 10,
  (78, '6'): 10,
  (78, '7'): 10,
  (78, '8'): 10,
  (78, '9'): 10,
  (78, 'A'): 10,
  (78, 'B'): 10,
  (78, 'C'): 10,
  (78, 'D'): 10,
  (78, 'E'): 10,
  (78, 'F'): 10,
  (78, 'G'): 10,
  (78, 'H'): 10,
  (78, 'I'): 10,
  (78, 'J'): 10,
  (78, 'K'): 10,
  (78, 'L'): 10,
  (78, 'M'): 10,
  (78, 'N'): 10,
  (78, 'O'): 10,
  (78, 'P'): 10,
  (78, 'Q'): 10,
  (78, 'R'): 10,
  (78, 'S'): 10,
  (78, 'T'): 10,
  (78, 'U'): 10,
  (78, 'V'): 10,
  (78, 'W'): 10,
  (78, 'X'): 10,
  (78, 'Y'): 10,
  (78, 'Z'): 10,
  (78, '_'): 10,
  (78, 'a'): 10,
  (78, 'b'): 10,
  (78, 'c'): 10,
  (78, 'd'): 10,
  (78, 'e'): 10,
  (78, 'f'): 10,
  (78, 'g'): 10,
  (78, 'h'): 10,
  (78, 'i'): 10,
  (78, 'j'): 10,
  (78, 'k'): 10,
  (78, 'l'): 10,
  (78, 'm'): 10,
  (78, 'n'): 10,
  (78, 'o'): 10,
  (78, 'p'): 10,
  (78, 'q'): 10,
  (78, 'r'): 79,
  (78, 's'): 10,
  (78, 't'): 10,
  (78, 'u'): 10,
  (78, 'v'): 10,
  (78, 'w'): 10,
  (78, 'x'): 10,
  (78, 'y'): 10,
  (78, 'z'): 10,
  (79, '0'): 10,
  (79, '1'): 10,
  (79, '2'): 10,
  (79, '3'): 10,
  (79, '4'): 10,
  (79, '5'): 10,
  (79, '6'): 10,
  (79, '7'): 10,
  (79, '8'): 10,
  (79, '9'): 10,
  (79, 'A'): 10,
  (79, 'B'): 10,
  (79, 'C'): 10,
  (79, 'D'): 10,
  (79, 'E'): 10,
  (79, 'F'): 10,
  (79, 'G'): 10,
  (79, 'H'): 10,
  (79, 'I'): 10,
  (79, 'J'): 10,
  (79, 'K'): 10,
  (79, 'L'): 10,
  (79, 'M'): 10,
  (79, 'N'): 10,
  (79, 'O'): 10,
  (79, 'P'): 10,
  (79, 'Q'): 10,
  (79, 'R'): 10,
  (79, 'S'): 10,
  (79, 'T'): 10,
  (79, 'U'): 10,
  (79, 'V'): 10,
  (79, 'W'): 10,
  (79, 'X'): 10,
  (79, 'Y'): 10,
  (79, 'Z'): 10,
  (79, '_'): 10,
  (79, 'a'): 10,
  (79, 'b'): 10,
  (79, 'c'): 10,
  (79, 'd'): 10,
  (79, 'e'): 10,
  (79, 'f'): 10,
  (79, 'g'): 10,
  (79, 'h'): 10,
  (79, 'i'): 10,
  (79, 'j'): 10,
  (79, 'k'): 10,
  (79, 'l'): 10,
  (79, 'm'): 10,
  (79, 'n'): 10,
  (79, 'o'): 10,
  (79, 'p'): 10,
  (79, 'q'): 10,
  (79, 'r'): 10,
  (79, 's'): 10,
  (79, 't'): 10,
  (79, 'u'): 10,
  (79, 'v'): 10,
  (79, 'w'): 10,
  (79, 'x'): 10,
  (79, 'y'): 10,
  (79, 'z'): 10,
  (81, '='): 83,
  (84, '<'): 88,
  (86, '='): 87,
  (90, '0'): 91,
  (90, '1'): 91,
  (90, '2'): 91,
  (90, '3'): 91,
  (90, '4'): 91,
  (90, '5'): 91,
  (90, '6'): 91,
  (90, '7'): 91,
  (90, '8'): 91,
  (90, '9'): 91,
  (91, '0'): 91,
  (91, '1'): 91,
  (91, '2'): 91,
  (91, '3'): 91,
  (91, '4'): 91,
  (91, '5'): 91,
  (91, '6'): 91,
  (91, '7'): 91,
  (91, '8'): 91,
  (91, '9'): 91},
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
      41,
      42,
      43,
      44,
      45,
      46,
      47,
      48,
      49,
      50,
      51,
      52,
      54,
      57,
      59,
      60,
      61,
      62,
      64,
      65,
      66,
      67,
      68,
      69,
      70,
      71,
      72,
      73,
      75,
      76,
      78,
      79,
      80,
      81,
      82,
      83,
      85,
      86,
      87,
      88,
      89,
      91]),
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
      41,
      42,
      43,
      44,
      45,
      46,
      47,
      48,
      49,
      50,
      51,
      52,
      54,
      57,
      59,
      60,
      61,
      62,
      64,
      65,
      66,
      67,
      68,
      69,
      70,
      71,
      72,
      73,
      75,
      76,
      78,
      79,
      80,
      81,
      82,
      83,
      85,
      86,
      87,
      88,
      89,
      91]),
 ['0, 0, 0, 0, start|, 0, start|, 0, 0, 0, 0, start|, 0, 0, 0, 0, 0, start|, 0, start|, 0, 0, start|, 0, 0, 0, 0, 0, 0, 0, start|, 0, start|, start|, 0, 0, start|, 0, start|, start|, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0',
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
