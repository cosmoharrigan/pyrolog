import py
from prolog.interpreter.test.tool import assert_true, assert_false, \
prolog_raises
from prolog.interpreter.continuation import Engine
from prolog.interpreter.parsing import get_engine

e = Engine(load_system=True)

def test_freeze():
    assert_true("freeze(X, Y = 1), X = 1, Y == 1.", e)
    assert_false("freeze(X, true), X = 1, attvar(X).", e)
    assert_false("freeze(X, Y = 1), X = 1, fail; Y == 1.", e)
    assert_true("freeze(a, Y = 1), Y == 1.", e)
    prolog_raises("existence_error(_, _)", "freeze(a, a)", e)
    assert_true("freeze(X, Y = 1), freeze(X, Z = 2), X = a, Y == 1, Z == 2.", e)
    assert_true("assert(f(a)).", e)
    assert_true("freeze(X, f(a)), X = 1.", e)
    assert_true("freeze(X, user:f(a)), X = 1.", e)
    assert_true("assert(m:g(q)).", e)
    assert_true("freeze(X, m:g(q)), X = 1.", e)
    assert_false("freeze(X, Y = 1), freeze(X, Y = 2), X = a.", e)
    assert_true("freeze(X, Y = 1), freeze(X, Z = 2), X = a, Y == 1, Z == 2.", e)

def test_when():
    prolog_raises("domain_error(_, _)", "when(var(X), f(a))", e)
    assert_true("when(nonvar(X), Y = 1), X = a, Y == 1.", e)
    assert_true("when(ground(f(X, Y)), Z = 1), X = 1, var(Z), Y = a, Z == 1.", e)
    assert_false("when(ground(f(X, Y)), Z = 1), X = 1, Z == 1.", e)
    assert_true("when(','(ground(X), ground(Y)), Z = 1), X = a, var(Z), Y = b, Z == 1.", e)
    assert_false("when(';'(ground(X), ground(Y)), Z = 1), X = a, var(Z), Y = b, Z == 1.", e)
    assert_true("when(';'(ground(X), ground(Y)), Z = 1), var(Z), Y = b, Z == 1.", e)
    assert_true("when(';'(ground(X), ground(Y)), Z = 1), var(Z), Y = b, Z == 1, X = a.", e)
    assert_true("when(?=(1, 1), X = a), X == a.", e)
    prolog_raises("instanciation_error", "when(X, X == 1)", e)
    prolog_raises("instanciation_error", "when(nonvar(a), X)", e)
    assert_true("when(nonvar(a), (X = 1, Y = 2)), X == 1, Y == 2.", e)
    assert_true("when(nonvar(a), f(a)).", e)
    assert_true("assert((z :- call(f(a)))).", e)
    assert_true("when(nonvar(a), z).", e)
    assert_true("when(nonvar(X), f(a)), X = 1.", e)
    assert_true("when(ground(1), m:g(q)).", e)
    assert_true("when(ground(X), Y = 1), when(ground(X), Z = 2), X = a, Y == 1, Z == 2.", e)
