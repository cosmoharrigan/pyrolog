import py
from prolog.interpreter.test.tool import assert_true, assert_false, prolog_raises

def test_declaration():
    assert_true("module(blub).")
    prolog_raises("existence_error(X, Y)", "module(bla, [f(a)])")
    assert_true("module(m), module(m).")
    prolog_raises("instantiation_error", "module(X)")

