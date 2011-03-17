import py
from prolog.interpreter.test.tool import prolog_raises, \
assert_true, assert_false
from prolog.interpreter.parsing import get_engine


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
    assert_true("put_attr(X, b, 1), (put_attr(X, b, 1), fail; get_attr(X, b, 1)).")

    e = get_engine("g(X) :- !, put_attr(X, m, 1), fail.")
    assert_true("\+ g(X), \+ attvar(X).", e)

def test_attvar_and_put_attr():
    assert_true("put_attr(X, m, 1), attvar(X).")
    assert_false("attvar(X), put_attr(X, m, 1).")

def test_get_attr():
    assert_true("put_attr(X, m, 1), get_attr(X, m, 1).")
    assert_false("get_attr(X, m, 1).")
    prolog_raises("type_error(A, B)", "get_attr(X, 2, 2)")
    prolog_raises("instantiation_error", "get_attr(X, Y, 2)")
    assert_true("put_attr(X, m, 1), put_attr(X, m, 2), get_attr(X, m, 2).")

def test_backtracking():
    assert_false("(put_attr(X, m, 1), fail); attvar(X).")
    assert_false("put_attr(X, m, 2), (put_attr(X, m, 1), fail); get_attr(X, m, 2).")
    assert_true("(put_attr(X, b, 1), fail); \+ get_attr(X, b, 1).")
    assert_true("put_attr(X, a, 2),  ((put_attr(X, b, 1), fail); get_attr(X, a, 2)), \+ get_attr(X, b, 1).")

def test_del_attr():
    assert_true("del_attr(X, m).")
    assert_true("del_attr(a, m).")
    prolog_raises("instantiation_error", "del_attr(X, Y)")
    prolog_raises("type_error(A, B)", "del_attr(X, 1)")
    assert_false("put_attr(X, m, 1), del_attr(X, m), attvar(X).")
    assert_true("""put_attr(X, m, 1), put_attr(X, m2, 2), 
                    del_attr(X, m), attvar(X).""")

def xtest_attr_unify_hook():
    e = get_engine("",
    m = """
    :- module(m, []).
    
    attr_unify_hook(Attr, Value) :-
        10 is Attr + Value.
    """)
    assert_true("put_attr(X, m, 1), X = 9.", e)
    assert_true("put_attr(X, m, 2), X = 8.", e)
    assert_false("put_attr(X, m, 1), X = 10.", e)
    assert_false("put_attr(X, m, 0), X = 11.", e)
