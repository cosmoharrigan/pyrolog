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

def test_get_attr():
    assert_true("put_attr(X, m, 1), get_attr(X, m, 1).")
    assert_false("get_attr(X, m, 1).")
    prolog_raises("type_error(A, B)", "get_attr(X, 2, 2)")
    prolog_raises("instantiation_error", "get_attr(X, Y, 2)")
    assert_true("put_attr(X, m, 1), put_attr(X, m, 2), get_attr(X, m, 2).")

def test_del_attr():
    assert_true("del_attr(X, m).")
    assert_true("del_attr(a, m).")
    prolog_raises("instantiation_error", "del_attr(X, Y)")
    prolog_raises("type_error(A, B)", "del_attr(X, 1)")
    assert_false("put_attr(X, m, 1), del_attr(X, m), attvar(X).")
    assert_true("""put_attr(X, m, 1), put_attr(X, m2, 2), 
                    del_attr(X, m), attvar(X).""")
