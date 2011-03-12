import py
from prolog.interpreter.test.tool import prolog_raises, \
assert_true, assert_false


def test_not_attvar():
    assert_false("attvar(1).")
    assert_false("attvar(X).")
    assert_false("attvar(a).")
    assert_false("attvar((a --> b)).")

def test_put_attr():
    assert_true("put_attr(X, m, 1).")
    assert_true("put_attr(X, m, abc).")
    assert_true("put_attr(X, m, Y).")
    prolog_raises("type_error(A, B)", "put_attr(X, 1, 1)")
    assert_true("put_attr(X, m1, 1), put_attr(X, m2, 1), put_attr(X, m1, 2).")

def test_attvar_and_put_attr():
    assert_true("put_attr(X, m, 1), attvar(X).")
    assert_false("attvar(X), put_attr(X, m, 1).")
