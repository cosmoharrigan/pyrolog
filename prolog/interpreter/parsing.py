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

def make_regexes():
    regexs = [
        ("VAR", parse_regex("[A-Z_]([a-zA-Z0-9]|_)*|_")),
        ("NUMBER", parse_regex("(0|[1-9][0-9]*)(\.[0-9]+)?")),
        ("IGNORE", parse_regex(
            "[ \\n\\t]|(/\\*[^\\*]*(\\*[^/][^\\*]*)*\\*/)|(%[^\\n]*)")),
        ("ATOM", parse_regex("([a-z]([a-zA-Z0-9]|_)*)|('[^']*')|\[\]|!|\+|\-")),
        ("STRING", parse_regex('"[^"]*"')),
        ("(", parse_regex("\(")),
        (")", parse_regex("\)")),
        ("[", parse_regex("\[")),
        ("]", parse_regex("\]")),
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
        from prolog.interpreter.term import String
        info = node.additional_info
        s = unicode(info[1:len(info) - 1], "utf8")
        code_points = []
        for i in range(len(s)):
            code_points.append(ord(s[i]))
        return String(info, code_points)

    def visit_complexterm(self, node):
        from prolog.interpreter.term import Callable
        name = self.general_symbol_visit(node.children[0]).name()
        children = self.build_list(node.children[2])
        return Callable.build(name, children[:])

    def visit_expr(self, node):
        from prolog.interpreter.term import Number, Float, BigInt
        if node.children[0].additional_info == '-':
            result = self.visit(node.children[1])
            if isinstance(result, Number):
                return Number(-result.num)
            elif isinstance(result, Float):
                return Float(-result.floatval)
        return self.visit(node.children[1])

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

def get_engine(source):
    from prolog.interpreter.continuation import Engine
    trees = parse_file(source)
    builder = TermBuilder()
    e = Engine()
    for fact in builder.build_many(trees):
        e.add_rule(fact)
    return e

# generated code between this line and its other occurence

parser_fact = PrologPackratParser([Rule('query', [['toplevel_op_expr', '.', 'EOF']]),
  Rule('fact', [['toplevel_op_expr', '.']]),
  Rule('complexterm', [['ATOM', '(', 'toplevel_op_expr', ')'], ['expr']]),
  Rule('expr', [['VAR'], ['NUMBER'], ['+', 'NUMBER'], ['-', 'NUMBER'], ['ATOM'], ['STRING'], ['(', 'toplevel_op_expr', ')'], ['listexpr']]),
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
  Rule('expr', [['VAR'], ['NUMBER'], ['+', 'NUMBER'], ['-', 'NUMBER'], ['ATOM'], ['STRING'], ['(', 'toplevel_op_expr', ')'], ['listexpr']]),
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
            elif char == '"':
                state = 19
            elif char == '*':
                state = 20
            elif char == '.':
                state = 21
            elif char == ':':
                state = 22
            elif char == '>':
                state = 23
            elif char == '^':
                state = 24
            elif char == 'r':
                state = 25
            elif char == '~':
                state = 26
            elif char == '!':
                state = 27
            elif char == '%':
                state = 28
            elif char == ')':
                state = 29
            elif char == '-':
                state = 30
            elif char == '=':
                state = 31
            elif char == ']':
                state = 32
            elif char == 'i':
                state = 33
            elif char == 'm':
                state = 34
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
                state = 75
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
                state = 75
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
                state = 74
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
                state = 69
            elif char == '<':
                state = 70
            elif char == '>':
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
                state = 65
            elif char == '=':
                state = 66
            elif char == '/':
                state = 67
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
                state = 63
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
                state = 27
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
                state = 59
            elif char == '\\':
                state = 60
            elif char == '/':
                state = 61
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
                state = 58
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
                state = 27
            else:
                break
        if state == 19:
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 19
                return ~i
            if char == '"':
                state = 57
            elif '#' <= char <= '\xff':
                state = 19
                continue
            elif '\x00' <= char <= '!':
                state = 19
                continue
            else:
                break
        if state == 20:
            runner.last_matched_index = i - 1
            runner.last_matched_state = state
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 20
                return i
            if char == '*':
                state = 56
            else:
                break
        if state == 22:
            runner.last_matched_index = i - 1
            runner.last_matched_state = state
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 22
                return i
            if char == '-':
                state = 55
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
            if char == '=':
                state = 53
            elif char == '>':
                state = 54
            else:
                break
        if state == 25:
            runner.last_matched_index = i - 1
            runner.last_matched_state = state
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 25
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
        if state == 28:
            runner.last_matched_index = i - 1
            runner.last_matched_state = state
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 28
                return i
            if '\x0b' <= char <= '\xff':
                state = 28
                continue
            elif '\x00' <= char <= '\t':
                state = 28
                continue
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
            if char == '-':
                state = 48
            elif char == '>':
                state = 49
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
            if char == '@':
                state = 38
            elif char == ':':
                state = 39
            elif char == '\\':
                state = 40
            elif char == '.':
                state = 41
            elif char == '=':
                state = 42
            elif char == '<':
                state = 43
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
                state = 37
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
                state = 35
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
                state = 36
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
        if state == 38:
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 38
                return ~i
            if char == '=':
                state = 47
            else:
                break
        if state == 39:
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 39
                return ~i
            if char == '=':
                state = 46
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
                state = 45
            else:
                break
        if state == 41:
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 41
                return ~i
            if char == '.':
                state = 44
            else:
                break
        if state == 48:
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 48
                return ~i
            if char == '>':
                state = 50
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
                state = 52
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
        if state == 59:
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 59
                return ~i
            if '+' <= char <= '\xff':
                state = 59
                continue
            elif '\x00' <= char <= ')':
                state = 59
                continue
            elif char == '*':
                state = 62
            else:
                break
        if state == 62:
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 62
                return ~i
            if char == '/':
                state = 1
            elif '0' <= char <= '\xff':
                state = 59
                continue
            elif '\x00' <= char <= '.':
                state = 59
                continue
            else:
                break
        if state == 63:
            runner.last_matched_index = i - 1
            runner.last_matched_state = state
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 63
                return i
            if char == 'r':
                state = 64
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
        if state == 64:
            runner.last_matched_index = i - 1
            runner.last_matched_state = state
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 64
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
        if state == 66:
            runner.last_matched_index = i - 1
            runner.last_matched_state = state
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 66
                return i
            if char == '=':
                state = 68
            else:
                break
        if state == 69:
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 69
                return ~i
            if char == '<':
                state = 73
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
            if char == '=':
                state = 72
            else:
                break
        if state == 75:
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 75
                return ~i
            if '0' <= char <= '9':
                state = 76
            else:
                break
        if state == 76:
            runner.last_matched_index = i - 1
            runner.last_matched_state = state
            try:
                char = input[i]
                i += 1
            except IndexError:
                runner.state = 76
                return i
            if '0' <= char <= '9':
                state = 76
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
lexer = DummyLexer(recognize, DFA(77,
 {(0, '\t'): 1,
  (0, '\n'): 1,
  (0, ' '): 1,
  (0, '!'): 27,
  (0, '"'): 19,
  (0, '%'): 28,
  (0, "'"): 13,
  (0, '('): 2,
  (0, ')'): 29,
  (0, '*'): 20,
  (0, '+'): 14,
  (0, ','): 3,
  (0, '-'): 30,
  (0, '.'): 21,
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
  (0, ':'): 22,
  (0, ';'): 16,
  (0, '<'): 6,
  (0, '='): 31,
  (0, '>'): 23,
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
  (0, ']'): 32,
  (0, '^'): 24,
  (0, '_'): 8,
  (0, 'a'): 10,
  (0, 'b'): 10,
  (0, 'c'): 10,
  (0, 'd'): 10,
  (0, 'e'): 10,
  (0, 'f'): 10,
  (0, 'g'): 10,
  (0, 'h'): 10,
  (0, 'i'): 33,
  (0, 'j'): 10,
  (0, 'k'): 10,
  (0, 'l'): 10,
  (0, 'm'): 34,
  (0, 'n'): 10,
  (0, 'o'): 10,
  (0, 'p'): 10,
  (0, 'q'): 10,
  (0, 'r'): 25,
  (0, 's'): 10,
  (0, 't'): 10,
  (0, 'u'): 10,
  (0, 'v'): 10,
  (0, 'w'): 10,
  (0, 'x'): 11,
  (0, 'y'): 10,
  (0, 'z'): 10,
  (0, '|'): 12,
  (0, '~'): 26,
  (4, '.'): 75,
  (5, '.'): 75,
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
  (6, '<'): 74,
  (7, '<'): 70,
  (7, '='): 69,
  (7, '>'): 71,
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
  (9, '+'): 65,
  (9, '/'): 67,
  (9, '='): 66,
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
  (11, 'o'): 63,
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
  (13, "'"): 27,
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
  (15, '*'): 59,
  (15, '/'): 61,
  (15, '\\'): 60,
  (17, '-'): 58,
  (18, ']'): 27,
  (19, '\x00'): 19,
  (19, '\x01'): 19,
  (19, '\x02'): 19,
  (19, '\x03'): 19,
  (19, '\x04'): 19,
  (19, '\x05'): 19,
  (19, '\x06'): 19,
  (19, '\x07'): 19,
  (19, '\x08'): 19,
  (19, '\t'): 19,
  (19, '\n'): 19,
  (19, '\x0b'): 19,
  (19, '\x0c'): 19,
  (19, '\r'): 19,
  (19, '\x0e'): 19,
  (19, '\x0f'): 19,
  (19, '\x10'): 19,
  (19, '\x11'): 19,
  (19, '\x12'): 19,
  (19, '\x13'): 19,
  (19, '\x14'): 19,
  (19, '\x15'): 19,
  (19, '\x16'): 19,
  (19, '\x17'): 19,
  (19, '\x18'): 19,
  (19, '\x19'): 19,
  (19, '\x1a'): 19,
  (19, '\x1b'): 19,
  (19, '\x1c'): 19,
  (19, '\x1d'): 19,
  (19, '\x1e'): 19,
  (19, '\x1f'): 19,
  (19, ' '): 19,
  (19, '!'): 19,
  (19, '"'): 57,
  (19, '#'): 19,
  (19, '$'): 19,
  (19, '%'): 19,
  (19, '&'): 19,
  (19, "'"): 19,
  (19, '('): 19,
  (19, ')'): 19,
  (19, '*'): 19,
  (19, '+'): 19,
  (19, ','): 19,
  (19, '-'): 19,
  (19, '.'): 19,
  (19, '/'): 19,
  (19, '0'): 19,
  (19, '1'): 19,
  (19, '2'): 19,
  (19, '3'): 19,
  (19, '4'): 19,
  (19, '5'): 19,
  (19, '6'): 19,
  (19, '7'): 19,
  (19, '8'): 19,
  (19, '9'): 19,
  (19, ':'): 19,
  (19, ';'): 19,
  (19, '<'): 19,
  (19, '='): 19,
  (19, '>'): 19,
  (19, '?'): 19,
  (19, '@'): 19,
  (19, 'A'): 19,
  (19, 'B'): 19,
  (19, 'C'): 19,
  (19, 'D'): 19,
  (19, 'E'): 19,
  (19, 'F'): 19,
  (19, 'G'): 19,
  (19, 'H'): 19,
  (19, 'I'): 19,
  (19, 'J'): 19,
  (19, 'K'): 19,
  (19, 'L'): 19,
  (19, 'M'): 19,
  (19, 'N'): 19,
  (19, 'O'): 19,
  (19, 'P'): 19,
  (19, 'Q'): 19,
  (19, 'R'): 19,
  (19, 'S'): 19,
  (19, 'T'): 19,
  (19, 'U'): 19,
  (19, 'V'): 19,
  (19, 'W'): 19,
  (19, 'X'): 19,
  (19, 'Y'): 19,
  (19, 'Z'): 19,
  (19, '['): 19,
  (19, '\\'): 19,
  (19, ']'): 19,
  (19, '^'): 19,
  (19, '_'): 19,
  (19, '`'): 19,
  (19, 'a'): 19,
  (19, 'b'): 19,
  (19, 'c'): 19,
  (19, 'd'): 19,
  (19, 'e'): 19,
  (19, 'f'): 19,
  (19, 'g'): 19,
  (19, 'h'): 19,
  (19, 'i'): 19,
  (19, 'j'): 19,
  (19, 'k'): 19,
  (19, 'l'): 19,
  (19, 'm'): 19,
  (19, 'n'): 19,
  (19, 'o'): 19,
  (19, 'p'): 19,
  (19, 'q'): 19,
  (19, 'r'): 19,
  (19, 's'): 19,
  (19, 't'): 19,
  (19, 'u'): 19,
  (19, 'v'): 19,
  (19, 'w'): 19,
  (19, 'x'): 19,
  (19, 'y'): 19,
  (19, 'z'): 19,
  (19, '{'): 19,
  (19, '|'): 19,
  (19, '}'): 19,
  (19, '~'): 19,
  (19, '\x7f'): 19,
  (19, '\x80'): 19,
  (19, '\x81'): 19,
  (19, '\x82'): 19,
  (19, '\x83'): 19,
  (19, '\x84'): 19,
  (19, '\x85'): 19,
  (19, '\x86'): 19,
  (19, '\x87'): 19,
  (19, '\x88'): 19,
  (19, '\x89'): 19,
  (19, '\x8a'): 19,
  (19, '\x8b'): 19,
  (19, '\x8c'): 19,
  (19, '\x8d'): 19,
  (19, '\x8e'): 19,
  (19, '\x8f'): 19,
  (19, '\x90'): 19,
  (19, '\x91'): 19,
  (19, '\x92'): 19,
  (19, '\x93'): 19,
  (19, '\x94'): 19,
  (19, '\x95'): 19,
  (19, '\x96'): 19,
  (19, '\x97'): 19,
  (19, '\x98'): 19,
  (19, '\x99'): 19,
  (19, '\x9a'): 19,
  (19, '\x9b'): 19,
  (19, '\x9c'): 19,
  (19, '\x9d'): 19,
  (19, '\x9e'): 19,
  (19, '\x9f'): 19,
  (19, '\xa0'): 19,
  (19, '\xa1'): 19,
  (19, '\xa2'): 19,
  (19, '\xa3'): 19,
  (19, '\xa4'): 19,
  (19, '\xa5'): 19,
  (19, '\xa6'): 19,
  (19, '\xa7'): 19,
  (19, '\xa8'): 19,
  (19, '\xa9'): 19,
  (19, '\xaa'): 19,
  (19, '\xab'): 19,
  (19, '\xac'): 19,
  (19, '\xad'): 19,
  (19, '\xae'): 19,
  (19, '\xaf'): 19,
  (19, '\xb0'): 19,
  (19, '\xb1'): 19,
  (19, '\xb2'): 19,
  (19, '\xb3'): 19,
  (19, '\xb4'): 19,
  (19, '\xb5'): 19,
  (19, '\xb6'): 19,
  (19, '\xb7'): 19,
  (19, '\xb8'): 19,
  (19, '\xb9'): 19,
  (19, '\xba'): 19,
  (19, '\xbb'): 19,
  (19, '\xbc'): 19,
  (19, '\xbd'): 19,
  (19, '\xbe'): 19,
  (19, '\xbf'): 19,
  (19, '\xc0'): 19,
  (19, '\xc1'): 19,
  (19, '\xc2'): 19,
  (19, '\xc3'): 19,
  (19, '\xc4'): 19,
  (19, '\xc5'): 19,
  (19, '\xc6'): 19,
  (19, '\xc7'): 19,
  (19, '\xc8'): 19,
  (19, '\xc9'): 19,
  (19, '\xca'): 19,
  (19, '\xcb'): 19,
  (19, '\xcc'): 19,
  (19, '\xcd'): 19,
  (19, '\xce'): 19,
  (19, '\xcf'): 19,
  (19, '\xd0'): 19,
  (19, '\xd1'): 19,
  (19, '\xd2'): 19,
  (19, '\xd3'): 19,
  (19, '\xd4'): 19,
  (19, '\xd5'): 19,
  (19, '\xd6'): 19,
  (19, '\xd7'): 19,
  (19, '\xd8'): 19,
  (19, '\xd9'): 19,
  (19, '\xda'): 19,
  (19, '\xdb'): 19,
  (19, '\xdc'): 19,
  (19, '\xdd'): 19,
  (19, '\xde'): 19,
  (19, '\xdf'): 19,
  (19, '\xe0'): 19,
  (19, '\xe1'): 19,
  (19, '\xe2'): 19,
  (19, '\xe3'): 19,
  (19, '\xe4'): 19,
  (19, '\xe5'): 19,
  (19, '\xe6'): 19,
  (19, '\xe7'): 19,
  (19, '\xe8'): 19,
  (19, '\xe9'): 19,
  (19, '\xea'): 19,
  (19, '\xeb'): 19,
  (19, '\xec'): 19,
  (19, '\xed'): 19,
  (19, '\xee'): 19,
  (19, '\xef'): 19,
  (19, '\xf0'): 19,
  (19, '\xf1'): 19,
  (19, '\xf2'): 19,
  (19, '\xf3'): 19,
  (19, '\xf4'): 19,
  (19, '\xf5'): 19,
  (19, '\xf6'): 19,
  (19, '\xf7'): 19,
  (19, '\xf8'): 19,
  (19, '\xf9'): 19,
  (19, '\xfa'): 19,
  (19, '\xfb'): 19,
  (19, '\xfc'): 19,
  (19, '\xfd'): 19,
  (19, '\xfe'): 19,
  (19, '\xff'): 19,
  (20, '*'): 56,
  (22, '-'): 55,
  (23, '='): 53,
  (23, '>'): 54,
  (25, '0'): 10,
  (25, '1'): 10,
  (25, '2'): 10,
  (25, '3'): 10,
  (25, '4'): 10,
  (25, '5'): 10,
  (25, '6'): 10,
  (25, '7'): 10,
  (25, '8'): 10,
  (25, '9'): 10,
  (25, 'A'): 10,
  (25, 'B'): 10,
  (25, 'C'): 10,
  (25, 'D'): 10,
  (25, 'E'): 10,
  (25, 'F'): 10,
  (25, 'G'): 10,
  (25, 'H'): 10,
  (25, 'I'): 10,
  (25, 'J'): 10,
  (25, 'K'): 10,
  (25, 'L'): 10,
  (25, 'M'): 10,
  (25, 'N'): 10,
  (25, 'O'): 10,
  (25, 'P'): 10,
  (25, 'Q'): 10,
  (25, 'R'): 10,
  (25, 'S'): 10,
  (25, 'T'): 10,
  (25, 'U'): 10,
  (25, 'V'): 10,
  (25, 'W'): 10,
  (25, 'X'): 10,
  (25, 'Y'): 10,
  (25, 'Z'): 10,
  (25, '_'): 10,
  (25, 'a'): 10,
  (25, 'b'): 10,
  (25, 'c'): 10,
  (25, 'd'): 10,
  (25, 'e'): 51,
  (25, 'f'): 10,
  (25, 'g'): 10,
  (25, 'h'): 10,
  (25, 'i'): 10,
  (25, 'j'): 10,
  (25, 'k'): 10,
  (25, 'l'): 10,
  (25, 'm'): 10,
  (25, 'n'): 10,
  (25, 'o'): 10,
  (25, 'p'): 10,
  (25, 'q'): 10,
  (25, 'r'): 10,
  (25, 's'): 10,
  (25, 't'): 10,
  (25, 'u'): 10,
  (25, 'v'): 10,
  (25, 'w'): 10,
  (25, 'x'): 10,
  (25, 'y'): 10,
  (25, 'z'): 10,
  (28, '\x00'): 28,
  (28, '\x01'): 28,
  (28, '\x02'): 28,
  (28, '\x03'): 28,
  (28, '\x04'): 28,
  (28, '\x05'): 28,
  (28, '\x06'): 28,
  (28, '\x07'): 28,
  (28, '\x08'): 28,
  (28, '\t'): 28,
  (28, '\x0b'): 28,
  (28, '\x0c'): 28,
  (28, '\r'): 28,
  (28, '\x0e'): 28,
  (28, '\x0f'): 28,
  (28, '\x10'): 28,
  (28, '\x11'): 28,
  (28, '\x12'): 28,
  (28, '\x13'): 28,
  (28, '\x14'): 28,
  (28, '\x15'): 28,
  (28, '\x16'): 28,
  (28, '\x17'): 28,
  (28, '\x18'): 28,
  (28, '\x19'): 28,
  (28, '\x1a'): 28,
  (28, '\x1b'): 28,
  (28, '\x1c'): 28,
  (28, '\x1d'): 28,
  (28, '\x1e'): 28,
  (28, '\x1f'): 28,
  (28, ' '): 28,
  (28, '!'): 28,
  (28, '"'): 28,
  (28, '#'): 28,
  (28, '$'): 28,
  (28, '%'): 28,
  (28, '&'): 28,
  (28, "'"): 28,
  (28, '('): 28,
  (28, ')'): 28,
  (28, '*'): 28,
  (28, '+'): 28,
  (28, ','): 28,
  (28, '-'): 28,
  (28, '.'): 28,
  (28, '/'): 28,
  (28, '0'): 28,
  (28, '1'): 28,
  (28, '2'): 28,
  (28, '3'): 28,
  (28, '4'): 28,
  (28, '5'): 28,
  (28, '6'): 28,
  (28, '7'): 28,
  (28, '8'): 28,
  (28, '9'): 28,
  (28, ':'): 28,
  (28, ';'): 28,
  (28, '<'): 28,
  (28, '='): 28,
  (28, '>'): 28,
  (28, '?'): 28,
  (28, '@'): 28,
  (28, 'A'): 28,
  (28, 'B'): 28,
  (28, 'C'): 28,
  (28, 'D'): 28,
  (28, 'E'): 28,
  (28, 'F'): 28,
  (28, 'G'): 28,
  (28, 'H'): 28,
  (28, 'I'): 28,
  (28, 'J'): 28,
  (28, 'K'): 28,
  (28, 'L'): 28,
  (28, 'M'): 28,
  (28, 'N'): 28,
  (28, 'O'): 28,
  (28, 'P'): 28,
  (28, 'Q'): 28,
  (28, 'R'): 28,
  (28, 'S'): 28,
  (28, 'T'): 28,
  (28, 'U'): 28,
  (28, 'V'): 28,
  (28, 'W'): 28,
  (28, 'X'): 28,
  (28, 'Y'): 28,
  (28, 'Z'): 28,
  (28, '['): 28,
  (28, '\\'): 28,
  (28, ']'): 28,
  (28, '^'): 28,
  (28, '_'): 28,
  (28, '`'): 28,
  (28, 'a'): 28,
  (28, 'b'): 28,
  (28, 'c'): 28,
  (28, 'd'): 28,
  (28, 'e'): 28,
  (28, 'f'): 28,
  (28, 'g'): 28,
  (28, 'h'): 28,
  (28, 'i'): 28,
  (28, 'j'): 28,
  (28, 'k'): 28,
  (28, 'l'): 28,
  (28, 'm'): 28,
  (28, 'n'): 28,
  (28, 'o'): 28,
  (28, 'p'): 28,
  (28, 'q'): 28,
  (28, 'r'): 28,
  (28, 's'): 28,
  (28, 't'): 28,
  (28, 'u'): 28,
  (28, 'v'): 28,
  (28, 'w'): 28,
  (28, 'x'): 28,
  (28, 'y'): 28,
  (28, 'z'): 28,
  (28, '{'): 28,
  (28, '|'): 28,
  (28, '}'): 28,
  (28, '~'): 28,
  (28, '\x7f'): 28,
  (28, '\x80'): 28,
  (28, '\x81'): 28,
  (28, '\x82'): 28,
  (28, '\x83'): 28,
  (28, '\x84'): 28,
  (28, '\x85'): 28,
  (28, '\x86'): 28,
  (28, '\x87'): 28,
  (28, '\x88'): 28,
  (28, '\x89'): 28,
  (28, '\x8a'): 28,
  (28, '\x8b'): 28,
  (28, '\x8c'): 28,
  (28, '\x8d'): 28,
  (28, '\x8e'): 28,
  (28, '\x8f'): 28,
  (28, '\x90'): 28,
  (28, '\x91'): 28,
  (28, '\x92'): 28,
  (28, '\x93'): 28,
  (28, '\x94'): 28,
  (28, '\x95'): 28,
  (28, '\x96'): 28,
  (28, '\x97'): 28,
  (28, '\x98'): 28,
  (28, '\x99'): 28,
  (28, '\x9a'): 28,
  (28, '\x9b'): 28,
  (28, '\x9c'): 28,
  (28, '\x9d'): 28,
  (28, '\x9e'): 28,
  (28, '\x9f'): 28,
  (28, '\xa0'): 28,
  (28, '\xa1'): 28,
  (28, '\xa2'): 28,
  (28, '\xa3'): 28,
  (28, '\xa4'): 28,
  (28, '\xa5'): 28,
  (28, '\xa6'): 28,
  (28, '\xa7'): 28,
  (28, '\xa8'): 28,
  (28, '\xa9'): 28,
  (28, '\xaa'): 28,
  (28, '\xab'): 28,
  (28, '\xac'): 28,
  (28, '\xad'): 28,
  (28, '\xae'): 28,
  (28, '\xaf'): 28,
  (28, '\xb0'): 28,
  (28, '\xb1'): 28,
  (28, '\xb2'): 28,
  (28, '\xb3'): 28,
  (28, '\xb4'): 28,
  (28, '\xb5'): 28,
  (28, '\xb6'): 28,
  (28, '\xb7'): 28,
  (28, '\xb8'): 28,
  (28, '\xb9'): 28,
  (28, '\xba'): 28,
  (28, '\xbb'): 28,
  (28, '\xbc'): 28,
  (28, '\xbd'): 28,
  (28, '\xbe'): 28,
  (28, '\xbf'): 28,
  (28, '\xc0'): 28,
  (28, '\xc1'): 28,
  (28, '\xc2'): 28,
  (28, '\xc3'): 28,
  (28, '\xc4'): 28,
  (28, '\xc5'): 28,
  (28, '\xc6'): 28,
  (28, '\xc7'): 28,
  (28, '\xc8'): 28,
  (28, '\xc9'): 28,
  (28, '\xca'): 28,
  (28, '\xcb'): 28,
  (28, '\xcc'): 28,
  (28, '\xcd'): 28,
  (28, '\xce'): 28,
  (28, '\xcf'): 28,
  (28, '\xd0'): 28,
  (28, '\xd1'): 28,
  (28, '\xd2'): 28,
  (28, '\xd3'): 28,
  (28, '\xd4'): 28,
  (28, '\xd5'): 28,
  (28, '\xd6'): 28,
  (28, '\xd7'): 28,
  (28, '\xd8'): 28,
  (28, '\xd9'): 28,
  (28, '\xda'): 28,
  (28, '\xdb'): 28,
  (28, '\xdc'): 28,
  (28, '\xdd'): 28,
  (28, '\xde'): 28,
  (28, '\xdf'): 28,
  (28, '\xe0'): 28,
  (28, '\xe1'): 28,
  (28, '\xe2'): 28,
  (28, '\xe3'): 28,
  (28, '\xe4'): 28,
  (28, '\xe5'): 28,
  (28, '\xe6'): 28,
  (28, '\xe7'): 28,
  (28, '\xe8'): 28,
  (28, '\xe9'): 28,
  (28, '\xea'): 28,
  (28, '\xeb'): 28,
  (28, '\xec'): 28,
  (28, '\xed'): 28,
  (28, '\xee'): 28,
  (28, '\xef'): 28,
  (28, '\xf0'): 28,
  (28, '\xf1'): 28,
  (28, '\xf2'): 28,
  (28, '\xf3'): 28,
  (28, '\xf4'): 28,
  (28, '\xf5'): 28,
  (28, '\xf6'): 28,
  (28, '\xf7'): 28,
  (28, '\xf8'): 28,
  (28, '\xf9'): 28,
  (28, '\xfa'): 28,
  (28, '\xfb'): 28,
  (28, '\xfc'): 28,
  (28, '\xfd'): 28,
  (28, '\xfe'): 28,
  (28, '\xff'): 28,
  (30, '-'): 48,
  (30, '>'): 49,
  (31, '.'): 41,
  (31, ':'): 39,
  (31, '<'): 43,
  (31, '='): 42,
  (31, '@'): 38,
  (31, '\\'): 40,
  (33, '0'): 10,
  (33, '1'): 10,
  (33, '2'): 10,
  (33, '3'): 10,
  (33, '4'): 10,
  (33, '5'): 10,
  (33, '6'): 10,
  (33, '7'): 10,
  (33, '8'): 10,
  (33, '9'): 10,
  (33, 'A'): 10,
  (33, 'B'): 10,
  (33, 'C'): 10,
  (33, 'D'): 10,
  (33, 'E'): 10,
  (33, 'F'): 10,
  (33, 'G'): 10,
  (33, 'H'): 10,
  (33, 'I'): 10,
  (33, 'J'): 10,
  (33, 'K'): 10,
  (33, 'L'): 10,
  (33, 'M'): 10,
  (33, 'N'): 10,
  (33, 'O'): 10,
  (33, 'P'): 10,
  (33, 'Q'): 10,
  (33, 'R'): 10,
  (33, 'S'): 10,
  (33, 'T'): 10,
  (33, 'U'): 10,
  (33, 'V'): 10,
  (33, 'W'): 10,
  (33, 'X'): 10,
  (33, 'Y'): 10,
  (33, 'Z'): 10,
  (33, '_'): 10,
  (33, 'a'): 10,
  (33, 'b'): 10,
  (33, 'c'): 10,
  (33, 'd'): 10,
  (33, 'e'): 10,
  (33, 'f'): 10,
  (33, 'g'): 10,
  (33, 'h'): 10,
  (33, 'i'): 10,
  (33, 'j'): 10,
  (33, 'k'): 10,
  (33, 'l'): 10,
  (33, 'm'): 10,
  (33, 'n'): 10,
  (33, 'o'): 10,
  (33, 'p'): 10,
  (33, 'q'): 10,
  (33, 'r'): 10,
  (33, 's'): 37,
  (33, 't'): 10,
  (33, 'u'): 10,
  (33, 'v'): 10,
  (33, 'w'): 10,
  (33, 'x'): 10,
  (33, 'y'): 10,
  (33, 'z'): 10,
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
  (34, 'o'): 35,
  (34, 'p'): 10,
  (34, 'q'): 10,
  (34, 'r'): 10,
  (34, 's'): 10,
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
  (35, 'd'): 36,
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
  (35, 's'): 10,
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
  (36, 'o'): 10,
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
  (37, 't'): 10,
  (37, 'u'): 10,
  (37, 'v'): 10,
  (37, 'w'): 10,
  (37, 'x'): 10,
  (37, 'y'): 10,
  (37, 'z'): 10,
  (38, '='): 47,
  (39, '='): 46,
  (40, '='): 45,
  (41, '.'): 44,
  (48, '>'): 50,
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
  (51, 'm'): 52,
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
  (59, '\x00'): 59,
  (59, '\x01'): 59,
  (59, '\x02'): 59,
  (59, '\x03'): 59,
  (59, '\x04'): 59,
  (59, '\x05'): 59,
  (59, '\x06'): 59,
  (59, '\x07'): 59,
  (59, '\x08'): 59,
  (59, '\t'): 59,
  (59, '\n'): 59,
  (59, '\x0b'): 59,
  (59, '\x0c'): 59,
  (59, '\r'): 59,
  (59, '\x0e'): 59,
  (59, '\x0f'): 59,
  (59, '\x10'): 59,
  (59, '\x11'): 59,
  (59, '\x12'): 59,
  (59, '\x13'): 59,
  (59, '\x14'): 59,
  (59, '\x15'): 59,
  (59, '\x16'): 59,
  (59, '\x17'): 59,
  (59, '\x18'): 59,
  (59, '\x19'): 59,
  (59, '\x1a'): 59,
  (59, '\x1b'): 59,
  (59, '\x1c'): 59,
  (59, '\x1d'): 59,
  (59, '\x1e'): 59,
  (59, '\x1f'): 59,
  (59, ' '): 59,
  (59, '!'): 59,
  (59, '"'): 59,
  (59, '#'): 59,
  (59, '$'): 59,
  (59, '%'): 59,
  (59, '&'): 59,
  (59, "'"): 59,
  (59, '('): 59,
  (59, ')'): 59,
  (59, '*'): 62,
  (59, '+'): 59,
  (59, ','): 59,
  (59, '-'): 59,
  (59, '.'): 59,
  (59, '/'): 59,
  (59, '0'): 59,
  (59, '1'): 59,
  (59, '2'): 59,
  (59, '3'): 59,
  (59, '4'): 59,
  (59, '5'): 59,
  (59, '6'): 59,
  (59, '7'): 59,
  (59, '8'): 59,
  (59, '9'): 59,
  (59, ':'): 59,
  (59, ';'): 59,
  (59, '<'): 59,
  (59, '='): 59,
  (59, '>'): 59,
  (59, '?'): 59,
  (59, '@'): 59,
  (59, 'A'): 59,
  (59, 'B'): 59,
  (59, 'C'): 59,
  (59, 'D'): 59,
  (59, 'E'): 59,
  (59, 'F'): 59,
  (59, 'G'): 59,
  (59, 'H'): 59,
  (59, 'I'): 59,
  (59, 'J'): 59,
  (59, 'K'): 59,
  (59, 'L'): 59,
  (59, 'M'): 59,
  (59, 'N'): 59,
  (59, 'O'): 59,
  (59, 'P'): 59,
  (59, 'Q'): 59,
  (59, 'R'): 59,
  (59, 'S'): 59,
  (59, 'T'): 59,
  (59, 'U'): 59,
  (59, 'V'): 59,
  (59, 'W'): 59,
  (59, 'X'): 59,
  (59, 'Y'): 59,
  (59, 'Z'): 59,
  (59, '['): 59,
  (59, '\\'): 59,
  (59, ']'): 59,
  (59, '^'): 59,
  (59, '_'): 59,
  (59, '`'): 59,
  (59, 'a'): 59,
  (59, 'b'): 59,
  (59, 'c'): 59,
  (59, 'd'): 59,
  (59, 'e'): 59,
  (59, 'f'): 59,
  (59, 'g'): 59,
  (59, 'h'): 59,
  (59, 'i'): 59,
  (59, 'j'): 59,
  (59, 'k'): 59,
  (59, 'l'): 59,
  (59, 'm'): 59,
  (59, 'n'): 59,
  (59, 'o'): 59,
  (59, 'p'): 59,
  (59, 'q'): 59,
  (59, 'r'): 59,
  (59, 's'): 59,
  (59, 't'): 59,
  (59, 'u'): 59,
  (59, 'v'): 59,
  (59, 'w'): 59,
  (59, 'x'): 59,
  (59, 'y'): 59,
  (59, 'z'): 59,
  (59, '{'): 59,
  (59, '|'): 59,
  (59, '}'): 59,
  (59, '~'): 59,
  (59, '\x7f'): 59,
  (59, '\x80'): 59,
  (59, '\x81'): 59,
  (59, '\x82'): 59,
  (59, '\x83'): 59,
  (59, '\x84'): 59,
  (59, '\x85'): 59,
  (59, '\x86'): 59,
  (59, '\x87'): 59,
  (59, '\x88'): 59,
  (59, '\x89'): 59,
  (59, '\x8a'): 59,
  (59, '\x8b'): 59,
  (59, '\x8c'): 59,
  (59, '\x8d'): 59,
  (59, '\x8e'): 59,
  (59, '\x8f'): 59,
  (59, '\x90'): 59,
  (59, '\x91'): 59,
  (59, '\x92'): 59,
  (59, '\x93'): 59,
  (59, '\x94'): 59,
  (59, '\x95'): 59,
  (59, '\x96'): 59,
  (59, '\x97'): 59,
  (59, '\x98'): 59,
  (59, '\x99'): 59,
  (59, '\x9a'): 59,
  (59, '\x9b'): 59,
  (59, '\x9c'): 59,
  (59, '\x9d'): 59,
  (59, '\x9e'): 59,
  (59, '\x9f'): 59,
  (59, '\xa0'): 59,
  (59, '\xa1'): 59,
  (59, '\xa2'): 59,
  (59, '\xa3'): 59,
  (59, '\xa4'): 59,
  (59, '\xa5'): 59,
  (59, '\xa6'): 59,
  (59, '\xa7'): 59,
  (59, '\xa8'): 59,
  (59, '\xa9'): 59,
  (59, '\xaa'): 59,
  (59, '\xab'): 59,
  (59, '\xac'): 59,
  (59, '\xad'): 59,
  (59, '\xae'): 59,
  (59, '\xaf'): 59,
  (59, '\xb0'): 59,
  (59, '\xb1'): 59,
  (59, '\xb2'): 59,
  (59, '\xb3'): 59,
  (59, '\xb4'): 59,
  (59, '\xb5'): 59,
  (59, '\xb6'): 59,
  (59, '\xb7'): 59,
  (59, '\xb8'): 59,
  (59, '\xb9'): 59,
  (59, '\xba'): 59,
  (59, '\xbb'): 59,
  (59, '\xbc'): 59,
  (59, '\xbd'): 59,
  (59, '\xbe'): 59,
  (59, '\xbf'): 59,
  (59, '\xc0'): 59,
  (59, '\xc1'): 59,
  (59, '\xc2'): 59,
  (59, '\xc3'): 59,
  (59, '\xc4'): 59,
  (59, '\xc5'): 59,
  (59, '\xc6'): 59,
  (59, '\xc7'): 59,
  (59, '\xc8'): 59,
  (59, '\xc9'): 59,
  (59, '\xca'): 59,
  (59, '\xcb'): 59,
  (59, '\xcc'): 59,
  (59, '\xcd'): 59,
  (59, '\xce'): 59,
  (59, '\xcf'): 59,
  (59, '\xd0'): 59,
  (59, '\xd1'): 59,
  (59, '\xd2'): 59,
  (59, '\xd3'): 59,
  (59, '\xd4'): 59,
  (59, '\xd5'): 59,
  (59, '\xd6'): 59,
  (59, '\xd7'): 59,
  (59, '\xd8'): 59,
  (59, '\xd9'): 59,
  (59, '\xda'): 59,
  (59, '\xdb'): 59,
  (59, '\xdc'): 59,
  (59, '\xdd'): 59,
  (59, '\xde'): 59,
  (59, '\xdf'): 59,
  (59, '\xe0'): 59,
  (59, '\xe1'): 59,
  (59, '\xe2'): 59,
  (59, '\xe3'): 59,
  (59, '\xe4'): 59,
  (59, '\xe5'): 59,
  (59, '\xe6'): 59,
  (59, '\xe7'): 59,
  (59, '\xe8'): 59,
  (59, '\xe9'): 59,
  (59, '\xea'): 59,
  (59, '\xeb'): 59,
  (59, '\xec'): 59,
  (59, '\xed'): 59,
  (59, '\xee'): 59,
  (59, '\xef'): 59,
  (59, '\xf0'): 59,
  (59, '\xf1'): 59,
  (59, '\xf2'): 59,
  (59, '\xf3'): 59,
  (59, '\xf4'): 59,
  (59, '\xf5'): 59,
  (59, '\xf6'): 59,
  (59, '\xf7'): 59,
  (59, '\xf8'): 59,
  (59, '\xf9'): 59,
  (59, '\xfa'): 59,
  (59, '\xfb'): 59,
  (59, '\xfc'): 59,
  (59, '\xfd'): 59,
  (59, '\xfe'): 59,
  (59, '\xff'): 59,
  (62, '\x00'): 59,
  (62, '\x01'): 59,
  (62, '\x02'): 59,
  (62, '\x03'): 59,
  (62, '\x04'): 59,
  (62, '\x05'): 59,
  (62, '\x06'): 59,
  (62, '\x07'): 59,
  (62, '\x08'): 59,
  (62, '\t'): 59,
  (62, '\n'): 59,
  (62, '\x0b'): 59,
  (62, '\x0c'): 59,
  (62, '\r'): 59,
  (62, '\x0e'): 59,
  (62, '\x0f'): 59,
  (62, '\x10'): 59,
  (62, '\x11'): 59,
  (62, '\x12'): 59,
  (62, '\x13'): 59,
  (62, '\x14'): 59,
  (62, '\x15'): 59,
  (62, '\x16'): 59,
  (62, '\x17'): 59,
  (62, '\x18'): 59,
  (62, '\x19'): 59,
  (62, '\x1a'): 59,
  (62, '\x1b'): 59,
  (62, '\x1c'): 59,
  (62, '\x1d'): 59,
  (62, '\x1e'): 59,
  (62, '\x1f'): 59,
  (62, ' '): 59,
  (62, '!'): 59,
  (62, '"'): 59,
  (62, '#'): 59,
  (62, '$'): 59,
  (62, '%'): 59,
  (62, '&'): 59,
  (62, "'"): 59,
  (62, '('): 59,
  (62, ')'): 59,
  (62, '*'): 59,
  (62, '+'): 59,
  (62, ','): 59,
  (62, '-'): 59,
  (62, '.'): 59,
  (62, '/'): 1,
  (62, '0'): 59,
  (62, '1'): 59,
  (62, '2'): 59,
  (62, '3'): 59,
  (62, '4'): 59,
  (62, '5'): 59,
  (62, '6'): 59,
  (62, '7'): 59,
  (62, '8'): 59,
  (62, '9'): 59,
  (62, ':'): 59,
  (62, ';'): 59,
  (62, '<'): 59,
  (62, '='): 59,
  (62, '>'): 59,
  (62, '?'): 59,
  (62, '@'): 59,
  (62, 'A'): 59,
  (62, 'B'): 59,
  (62, 'C'): 59,
  (62, 'D'): 59,
  (62, 'E'): 59,
  (62, 'F'): 59,
  (62, 'G'): 59,
  (62, 'H'): 59,
  (62, 'I'): 59,
  (62, 'J'): 59,
  (62, 'K'): 59,
  (62, 'L'): 59,
  (62, 'M'): 59,
  (62, 'N'): 59,
  (62, 'O'): 59,
  (62, 'P'): 59,
  (62, 'Q'): 59,
  (62, 'R'): 59,
  (62, 'S'): 59,
  (62, 'T'): 59,
  (62, 'U'): 59,
  (62, 'V'): 59,
  (62, 'W'): 59,
  (62, 'X'): 59,
  (62, 'Y'): 59,
  (62, 'Z'): 59,
  (62, '['): 59,
  (62, '\\'): 59,
  (62, ']'): 59,
  (62, '^'): 59,
  (62, '_'): 59,
  (62, '`'): 59,
  (62, 'a'): 59,
  (62, 'b'): 59,
  (62, 'c'): 59,
  (62, 'd'): 59,
  (62, 'e'): 59,
  (62, 'f'): 59,
  (62, 'g'): 59,
  (62, 'h'): 59,
  (62, 'i'): 59,
  (62, 'j'): 59,
  (62, 'k'): 59,
  (62, 'l'): 59,
  (62, 'm'): 59,
  (62, 'n'): 59,
  (62, 'o'): 59,
  (62, 'p'): 59,
  (62, 'q'): 59,
  (62, 'r'): 59,
  (62, 's'): 59,
  (62, 't'): 59,
  (62, 'u'): 59,
  (62, 'v'): 59,
  (62, 'w'): 59,
  (62, 'x'): 59,
  (62, 'y'): 59,
  (62, 'z'): 59,
  (62, '{'): 59,
  (62, '|'): 59,
  (62, '}'): 59,
  (62, '~'): 59,
  (62, '\x7f'): 59,
  (62, '\x80'): 59,
  (62, '\x81'): 59,
  (62, '\x82'): 59,
  (62, '\x83'): 59,
  (62, '\x84'): 59,
  (62, '\x85'): 59,
  (62, '\x86'): 59,
  (62, '\x87'): 59,
  (62, '\x88'): 59,
  (62, '\x89'): 59,
  (62, '\x8a'): 59,
  (62, '\x8b'): 59,
  (62, '\x8c'): 59,
  (62, '\x8d'): 59,
  (62, '\x8e'): 59,
  (62, '\x8f'): 59,
  (62, '\x90'): 59,
  (62, '\x91'): 59,
  (62, '\x92'): 59,
  (62, '\x93'): 59,
  (62, '\x94'): 59,
  (62, '\x95'): 59,
  (62, '\x96'): 59,
  (62, '\x97'): 59,
  (62, '\x98'): 59,
  (62, '\x99'): 59,
  (62, '\x9a'): 59,
  (62, '\x9b'): 59,
  (62, '\x9c'): 59,
  (62, '\x9d'): 59,
  (62, '\x9e'): 59,
  (62, '\x9f'): 59,
  (62, '\xa0'): 59,
  (62, '\xa1'): 59,
  (62, '\xa2'): 59,
  (62, '\xa3'): 59,
  (62, '\xa4'): 59,
  (62, '\xa5'): 59,
  (62, '\xa6'): 59,
  (62, '\xa7'): 59,
  (62, '\xa8'): 59,
  (62, '\xa9'): 59,
  (62, '\xaa'): 59,
  (62, '\xab'): 59,
  (62, '\xac'): 59,
  (62, '\xad'): 59,
  (62, '\xae'): 59,
  (62, '\xaf'): 59,
  (62, '\xb0'): 59,
  (62, '\xb1'): 59,
  (62, '\xb2'): 59,
  (62, '\xb3'): 59,
  (62, '\xb4'): 59,
  (62, '\xb5'): 59,
  (62, '\xb6'): 59,
  (62, '\xb7'): 59,
  (62, '\xb8'): 59,
  (62, '\xb9'): 59,
  (62, '\xba'): 59,
  (62, '\xbb'): 59,
  (62, '\xbc'): 59,
  (62, '\xbd'): 59,
  (62, '\xbe'): 59,
  (62, '\xbf'): 59,
  (62, '\xc0'): 59,
  (62, '\xc1'): 59,
  (62, '\xc2'): 59,
  (62, '\xc3'): 59,
  (62, '\xc4'): 59,
  (62, '\xc5'): 59,
  (62, '\xc6'): 59,
  (62, '\xc7'): 59,
  (62, '\xc8'): 59,
  (62, '\xc9'): 59,
  (62, '\xca'): 59,
  (62, '\xcb'): 59,
  (62, '\xcc'): 59,
  (62, '\xcd'): 59,
  (62, '\xce'): 59,
  (62, '\xcf'): 59,
  (62, '\xd0'): 59,
  (62, '\xd1'): 59,
  (62, '\xd2'): 59,
  (62, '\xd3'): 59,
  (62, '\xd4'): 59,
  (62, '\xd5'): 59,
  (62, '\xd6'): 59,
  (62, '\xd7'): 59,
  (62, '\xd8'): 59,
  (62, '\xd9'): 59,
  (62, '\xda'): 59,
  (62, '\xdb'): 59,
  (62, '\xdc'): 59,
  (62, '\xdd'): 59,
  (62, '\xde'): 59,
  (62, '\xdf'): 59,
  (62, '\xe0'): 59,
  (62, '\xe1'): 59,
  (62, '\xe2'): 59,
  (62, '\xe3'): 59,
  (62, '\xe4'): 59,
  (62, '\xe5'): 59,
  (62, '\xe6'): 59,
  (62, '\xe7'): 59,
  (62, '\xe8'): 59,
  (62, '\xe9'): 59,
  (62, '\xea'): 59,
  (62, '\xeb'): 59,
  (62, '\xec'): 59,
  (62, '\xed'): 59,
  (62, '\xee'): 59,
  (62, '\xef'): 59,
  (62, '\xf0'): 59,
  (62, '\xf1'): 59,
  (62, '\xf2'): 59,
  (62, '\xf3'): 59,
  (62, '\xf4'): 59,
  (62, '\xf5'): 59,
  (62, '\xf6'): 59,
  (62, '\xf7'): 59,
  (62, '\xf8'): 59,
  (62, '\xf9'): 59,
  (62, '\xfa'): 59,
  (62, '\xfb'): 59,
  (62, '\xfc'): 59,
  (62, '\xfd'): 59,
  (62, '\xfe'): 59,
  (62, '\xff'): 59,
  (63, '0'): 10,
  (63, '1'): 10,
  (63, '2'): 10,
  (63, '3'): 10,
  (63, '4'): 10,
  (63, '5'): 10,
  (63, '6'): 10,
  (63, '7'): 10,
  (63, '8'): 10,
  (63, '9'): 10,
  (63, 'A'): 10,
  (63, 'B'): 10,
  (63, 'C'): 10,
  (63, 'D'): 10,
  (63, 'E'): 10,
  (63, 'F'): 10,
  (63, 'G'): 10,
  (63, 'H'): 10,
  (63, 'I'): 10,
  (63, 'J'): 10,
  (63, 'K'): 10,
  (63, 'L'): 10,
  (63, 'M'): 10,
  (63, 'N'): 10,
  (63, 'O'): 10,
  (63, 'P'): 10,
  (63, 'Q'): 10,
  (63, 'R'): 10,
  (63, 'S'): 10,
  (63, 'T'): 10,
  (63, 'U'): 10,
  (63, 'V'): 10,
  (63, 'W'): 10,
  (63, 'X'): 10,
  (63, 'Y'): 10,
  (63, 'Z'): 10,
  (63, '_'): 10,
  (63, 'a'): 10,
  (63, 'b'): 10,
  (63, 'c'): 10,
  (63, 'd'): 10,
  (63, 'e'): 10,
  (63, 'f'): 10,
  (63, 'g'): 10,
  (63, 'h'): 10,
  (63, 'i'): 10,
  (63, 'j'): 10,
  (63, 'k'): 10,
  (63, 'l'): 10,
  (63, 'm'): 10,
  (63, 'n'): 10,
  (63, 'o'): 10,
  (63, 'p'): 10,
  (63, 'q'): 10,
  (63, 'r'): 64,
  (63, 's'): 10,
  (63, 't'): 10,
  (63, 'u'): 10,
  (63, 'v'): 10,
  (63, 'w'): 10,
  (63, 'x'): 10,
  (63, 'y'): 10,
  (63, 'z'): 10,
  (64, '0'): 10,
  (64, '1'): 10,
  (64, '2'): 10,
  (64, '3'): 10,
  (64, '4'): 10,
  (64, '5'): 10,
  (64, '6'): 10,
  (64, '7'): 10,
  (64, '8'): 10,
  (64, '9'): 10,
  (64, 'A'): 10,
  (64, 'B'): 10,
  (64, 'C'): 10,
  (64, 'D'): 10,
  (64, 'E'): 10,
  (64, 'F'): 10,
  (64, 'G'): 10,
  (64, 'H'): 10,
  (64, 'I'): 10,
  (64, 'J'): 10,
  (64, 'K'): 10,
  (64, 'L'): 10,
  (64, 'M'): 10,
  (64, 'N'): 10,
  (64, 'O'): 10,
  (64, 'P'): 10,
  (64, 'Q'): 10,
  (64, 'R'): 10,
  (64, 'S'): 10,
  (64, 'T'): 10,
  (64, 'U'): 10,
  (64, 'V'): 10,
  (64, 'W'): 10,
  (64, 'X'): 10,
  (64, 'Y'): 10,
  (64, 'Z'): 10,
  (64, '_'): 10,
  (64, 'a'): 10,
  (64, 'b'): 10,
  (64, 'c'): 10,
  (64, 'd'): 10,
  (64, 'e'): 10,
  (64, 'f'): 10,
  (64, 'g'): 10,
  (64, 'h'): 10,
  (64, 'i'): 10,
  (64, 'j'): 10,
  (64, 'k'): 10,
  (64, 'l'): 10,
  (64, 'm'): 10,
  (64, 'n'): 10,
  (64, 'o'): 10,
  (64, 'p'): 10,
  (64, 'q'): 10,
  (64, 'r'): 10,
  (64, 's'): 10,
  (64, 't'): 10,
  (64, 'u'): 10,
  (64, 'v'): 10,
  (64, 'w'): 10,
  (64, 'x'): 10,
  (64, 'y'): 10,
  (64, 'z'): 10,
  (66, '='): 68,
  (69, '<'): 73,
  (71, '='): 72,
  (75, '0'): 76,
  (75, '1'): 76,
  (75, '2'): 76,
  (75, '3'): 76,
  (75, '4'): 76,
  (75, '5'): 76,
  (75, '6'): 76,
  (75, '7'): 76,
  (75, '8'): 76,
  (75, '9'): 76,
  (76, '0'): 76,
  (76, '1'): 76,
  (76, '2'): 76,
  (76, '3'): 76,
  (76, '4'): 76,
  (76, '5'): 76,
  (76, '6'): 76,
  (76, '7'): 76,
  (76, '8'): 76,
  (76, '9'): 76},
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
      20,
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
      42,
      43,
      44,
      45,
      46,
      47,
      49,
      50,
      51,
      52,
      53,
      54,
      55,
      56,
      57,
      58,
      60,
      61,
      63,
      64,
      65,
      66,
      67,
      68,
      70,
      71,
      72,
      73,
      74,
      76]),
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
      20,
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
      42,
      43,
      44,
      45,
      46,
      47,
      49,
      50,
      51,
      52,
      53,
      54,
      55,
      56,
      57,
      58,
      60,
      61,
      63,
      64,
      65,
      66,
      67,
      68,
      70,
      71,
      72,
      73,
      74,
      76]),
 ['0, 0, 0, start|, 0, start|, 0, 0, 0, 0, 0, start|, 0, 0, 0, 0, start|, 0, start|, 0, 0, start|, 0, 0, 0, 0, 0, 0, 0, start|, 0, start|, 0, 0, start|, 0, start|, start|, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0',
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
