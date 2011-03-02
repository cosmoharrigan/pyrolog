import py
from prolog.interpreter.test.tool import assert_true, get_engine
from prolog.interpreter.continuation import Engine

loc = "../../prolog_modules/"
e = get_engine("""
:- use_module('%s%s').
""" % (loc, "dcg"))

def test_a_to_b():
    assert_true("""
    trans((a --> b), X),
    X = (a(X1, X2) :- b(X1, X2)).
    """, e)

def test_a_to_b_c():
    assert_true("""
    trans((a --> b, c), X),
    X = (a(X1, X3) :- b(X1, X2), c(X2, X3)).
    """, e)

def test_single_terminal():
    assert_true("""
    trans((a --> [b]), X),
    X = (a([b|X1], X1) :- true).
    """, e)

def test_terminal_nonterminal():
    assert_true("""
    trans((a --> [c], b), X),
    X = (a([c|Y1], Y2) :- b(Y1, Y2)).
    """, e)

def test_nonterminal_terminal():
    assert_true("""
    trans((a --> b, [c]), X),
    X = (a(X1, X3) :- b(X1, X2), X2=[c|X3]).
    """, e)

def test_nonterminal_terminal_terminal():
    assert_true("""
    trans((a --> b, [c], [d]), X),
    X = (a(X1, X3) :- b(X1, X2), X2=[c, d|X3]).
    """, e)

def test_terminal_terminal():
    assert_true("""
    trans((a --> [b], [c]), X),
    X = (a([b, c|X], X) :- true).
    """, e)

def test_nonterminal_param_1():
    assert_true("""
    trans((a(X) --> b), R),
    R = (a(X, X1, X2) :- b(X1, X2)).
    """, e)

def test_nonterminal_param_2():
    assert_true("""
    trans((a(X, Y) --> b(Y)), R),
    R = (a(X, Y, X1, X2) :- b(Y, X1, X2)).
    """, e)

def test_curly():
    assert_true("""
    trans((a --> {X=1}), R),
    R = (a(X1, X2) :- X=1, X2=X1).
    """, e)

def test_nonterminal_curly():
    assert_true("""
    trans((a --> b, {X=1}), R),
    R = (a(X1, X2) :- b(X1, X3), X=1, X2=X3).
    """, e)

def test_nonterminal_nonterminal_curly():
    assert_true("""
    trans((a --> b, c, {X=1}), R),
    R = (a(X1, X2) :- b(X1, X3), c(X3, X4), X=1, X2=X4).
    """, e)

def test_curly_nonterminal():
    assert_true("""
    trans((a --> {X=1}, b), R),
    R = (a(X1, X2) :- X=1, b(X1, X2)).
    """, e)

def test_curly_multiple_nonterminal():
    assert_true("""
    trans((a --> {X=1, Y=2, Z=3}, b), R),
    R = (a(X1, X2) :- (X=1, Y=2, Z=3), b(X1, X2)).
    """, e)

def test_curly_nonterminal_curly_nonterminal():
    assert_true("""
    trans((a --> {X=1}, b, {Y=2}, c), R),
    R = (a(X1, X2) :- X=1, b(X1, X3), Y=2, c(X3, X2)).
    """, e)

def test_curly_terminal():
    assert_true("""
    trans((a --> {X=1}, [b]), R),
    R = (a(X1, X2) :- X=1, X1=[b|X2]).
    """, e)

def test_dcg_integration_1():
    assert_true("""
    trans((a --> {X=1, Y=2}, [b, c], b(Y)), R),
    R = (a(X1, X2) :- (X=1, Y=2), X1=[b, c|X4], b(Y, X4, X2)).
    """, e)

def test_curly_multiple_1():
    assert_true("""
    trans((a --> {X=1, Y=2}), R),
    R = (a(X1, X2) :- X=1, Y=2, X1=X2).
    """, e)

def test_curly_multiple_2():
    assert_true("""
    trans((a --> {X=1, Y=2, Z=3}), R),
    R = (a(X1, X2) :- X=1, Y=2, Z=3, X1=X2).
    """, e)
