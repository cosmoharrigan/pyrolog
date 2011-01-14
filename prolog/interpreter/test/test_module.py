import py
from prolog.interpreter.test.tool import get_engine, assert_true, assert_false, prolog_raises

def test_declaration():
    assert_true("module(blub).")
    #assert_true("module(m), module(m).")
    prolog_raises("instantiation_error", "module(X)")

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
    assert_true("both(X, Y), X == a, Y == b.", e)
