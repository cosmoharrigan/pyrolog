import py
from prolog.interpreter.test.tool import assert_true, assert_false, \
prolog_raises
from prolog.interpreter.continuation import Engine
from prolog.interpreter.parsing import get_engine

e = Engine(load_system=True)

def test_basic_freeze():
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
