import py
from prolog.interpreter.test.tool import prolog_raises, \
assert_true, assert_false


def test_not_attvar():
    assert_false("attvar(1).")
    assert_false("attvar(X).")
    assert_false("attvar(a).")
    assert_false("attvar((a --> b)).")
