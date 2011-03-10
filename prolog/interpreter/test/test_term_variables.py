import py
from prolog.interpreter.test.tool import assert_true, assert_false, prolog_raises

def test_basic_term_variables():
    assert_true("term_variables(X, [X]).")
    assert_false("term_variables(X, []).")
    assert_true("term_variables(f(X, Y), [X, Y]).")
    assert_true("term_variables(a, []).")
    assert_true("term_variables(123, []).")
    assert_true("term_variables(f(Z, g(X), Y), [Z, X, Y]).")
    assert_false("term_variables(a, a).")

def test_more_advanced_term_variables():
    assert_true("term_variables([X, Y, a, f(g(A), X)], [X, Y, A]).")
    assert_true("term_variables((A :- B, C, A), [A,B,C]).")
    assert_true("term_variables(f(X, f(X)), [X]).")
    assert_true("X = 1, term_variables(f(X, Y), L), Y = 2.")

def test_var_binding():
    assert_true("X = a, term_variables(X, []).")
    assert_true("term_variables(X, L), X = a, L = [a].")
    assert_true("X = f(A,B), term_variables(X, [A,B]).")

