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


def test_module_uses():
    e = get_engine("""
    :- use_module(b).
    """,
    b = """
    :- module(b, [f/1]).
    :- use_module(a).
    f(X) :- h(X).
    g(a).
    """,
    a = """
    :- module(a, [h/1]).
    h(z).
    """)

    assert len(e.modules) == 3
    assert e.modules["b"].uses == ["a"]
    assert e.modules["a"].uses == []
    assert e.modules["user"].uses == ["b"]


def test_fetch_function():
    e = get_engine("""
    :- use_module(m).
    f(a) :- g(a, b).
    """,
    m = """
    :- module(m, [g/2]).
    g(a, b).
    h(w).
    """)

    f_sig = Signature.getsignature("f", 1)
    g_sig = Signature.getsignature("g", 2)
    h_sig = Signature.getsignature("h", 1)
    user = e.modules["user"]
    m = e.modules["m"]

    assert user.fetch_function(f_sig) == user.functions[f_sig]
    assert user.fetch_function(g_sig) == m.functions[g_sig]
    assert user.fetch_function(h_sig) is None
    assert m.fetch_function(g_sig) == m.functions[g_sig]
    assert m.fetch_function(f_sig) is None
    assert m.fetch_function(h_sig) == m.functions[h_sig]


def test_modules_use_module():
    e = get_engine("""
    :- use_module(m).
    f(X) :- g(X).
    f(b).
    h(a).
    """, 
    m = """
    :- module(m, [g/1]).
    g(a).
    h(b).
    """)
    assert_true("f(a).", e)
    assert_true("f(b).", e)
    assert_true("h(a).", e)
    assert_false("h(b).", e)


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


def test_builtin_module_or():
    e = get_engine("""
    :- use_module(m).
    t :- h, x.
    x.
    """,
    m = """
    :- module(m, [h/0]).
    h :- f; g.
    f.
    g.
    """)
    assert_true("t.", e)


def test_builtin_module_and():
    e = get_engine("""
    :- use_module(m).
    t :- h, x.
    x.
    """,
    m = """
    :- module(m, [h/0]).
    h :- f, g.
    f.
    g.
    """)
    assert_true("t.", e)


def test_catch_error():
    e = get_engine("""
    :- use_module(m).
    h :- catch(f, X, g).
    g.
    """,
    m = """
    :- module(m, [f/0]).
    f :- throw(foo).
    """)
    assert_true("h.", e)
