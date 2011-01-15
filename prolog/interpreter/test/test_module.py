import py
from prolog.interpreter.test.tool import get_engine, assert_true, assert_false, prolog_raises
from prolog.interpreter import term
from prolog.interpreter.signature import Signature

def test_set_currently_parsed_module():
    e = get_engine("""
    f(a).
    """)
    assert e.currently_parsed_module == e.user_module
    e.set_currently_parsed_module("m1", [])
    assert "m1" in e.modules
    mod1 = e.modules["m1"]
    assert mod1.exports == []
    assert mod1.functions == {}
    atom = term.Callable.build("f")
    e.add_rule(atom)
    assert atom.signature() in mod1.functions


def test_module_exports():
    e = get_engine("""
    :- module(m, [g/2]).
    g(a, b).
    f(c, d, e).
    """)
    exports = e.modules["m"].exports
    assert len(exports) == 1 and exports[0].eq(Signature("g", 2))


def test_modules_integration():
    e = get_engine("""
        :- use_module(m).
        f(X) :- g(X).
        h(b).
        both(X, Y) :- f(X), h(Y).
    """,
    m = """
        :- module(m, [g/1]).
        g(X) :- h(X).
        h(a).
        """)
    assert_true("findall(X, h(X), L), L = [b].", e)
    assert_true("both(X, Y), X == a, Y == b.", e)
