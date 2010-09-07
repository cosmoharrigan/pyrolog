import py
from prolog.interpreter.error import UnificationFailed
from prolog.interpreter.term import Atom, Var, Number, Callable, Term
from prolog.interpreter.term import NumberedVar
from prolog.interpreter.continuation import Heap, Engine
from prolog.interpreter.helper import is_term

def test_atom():
    a = Callable.build("hallo")
    b = Callable.build("hallo")
    # does not raise
    a.unify(b, None)
    py.test.raises(UnificationFailed, "a.unify(Callable.build('xxx'), None)")

def test_var():
    b = Var()
    heap = Heap()
    b.unify(Callable.build("hallo"), heap)
    assert b.getvalue(heap).name()== "hallo"
    a = Var()
    b = Var()
    a.unify(b, heap)
    a.unify(Callable.build("hallo"), heap)
    assert a.getvalue(heap).name()== "hallo"
    assert b.getvalue(heap).name()== "hallo"

def test_unify_var():
    b = Var()
    heap = Heap()
    b.unify(b, heap)
    b.unify(Callable.build("hallo"), heap)
    py.test.raises(UnificationFailed, b.unify, Callable.build("bye"), heap)

def test_recursive():
    b = Var()
    heap = Heap()
    b.unify(Callable.build("hallo", [b]), heap)

def test_term():
    X = Var()
    Y = Var()
    t1 = Callable.build("f", [Callable.build("hallo"), X])
    t2 = Callable.build("f", [Y, Callable.build("HALLO")])
    heap = Heap()
    print t1, t2
    t1.unify(t2, heap)
    assert X.getvalue(heap).name()== "HALLO"
    assert Y.getvalue(heap).name()== "hallo"

def test_enumerate_vars():
    from prolog.interpreter.memo import EnumerationMemo
    X = Var()
    Y = Var()
    t1 = Callable.build("f", [X, X, Callable.build("g", [Y, X])])
    memo = EnumerationMemo()
    t2 = t1.enumerate_vars(memo)
    assert is_term(t2)
    assert t2.signature().eq(t1.signature())
    assert t2.argument_at(0) is t2.argument_at(1)
    assert t2.argument_at(0).num == 0
    assert t2.argument_at(2).argument_at(1).num == 0

def test_enumerate_vars_var_occurs_once():
    from prolog.interpreter.memo import EnumerationMemo
    X = Var()
    Y = Var()
    Z = Var()
    t1 = Callable.build("f", [X, Y, Y, Z, Z])
    memo = EnumerationMemo()
    t2 = t1.enumerate_vars(memo)
    assert t2.argument_at(0).num == -1
    assert t2.argument_at(1).num == 0
    assert t2.argument_at(2).num == 0
    assert t2.argument_at(3).num == 1
    assert t2.argument_at(4).num == 1

def test_unify_and_standardize_apart():
    heap = Heap()
    X = Var()
    Y = Var()
    Z = NumberedVar(0)
    t1 = Callable.build("f", [Z, Callable.build("g", [Z, Callable.build("h")]), Z])
    t2 = Callable.build("f", [Callable.build("i"), X, Y])
    env = [None]
    t1.unify_and_standardize_apart(t2, heap, env)

    Z = NumberedVar(-1)
    Z.unify_and_standardize_apart(t2, heap, [])

def test_copy_standardize_apart():
    heap = Heap()
    Z = NumberedVar(0)
    t = Callable.build("f", [Z, Z])
    t2 = t.copy_standardize_apart(heap, [None])
    assert isinstance(t2.argument_at(0), Var)
    assert t2.argument_at(0) is t2.argument_at(1)

    t2 = t.copy_standardize_apart(heap, [Number(1)])
    assert isinstance(t2.argument_at(0), Number)
    assert t2.argument_at(0) is t2.argument_at(1)

    Z = NumberedVar(-1)
    t = Callable.build("f", [Z, Z])
    t2 = t.copy_standardize_apart(heap, [None])
    assert isinstance(t2.argument_at(0), Var)
    assert isinstance(t2.argument_at(1), Var)
    assert t2.argument_at(0) is not t2.argument_at(1)

def test_run():
    e = Engine()
    e.add_rule(Callable.build("f", [Callable.build("a"), Callable.build("b")]))
    X = Var()
    Y = Var()
    c = Callable.build("f", [X, X])
    e.add_rule(c)
    c2 = Callable.build(":-", [Callable.build("f", [X, Y]),
                           Callable.build("f", [Y, X])])
    e.add_rule(c2)
    X = e.heap.newvar()
    c3 = Callable.build("f", [Callable.build("b"), X])
    e.run(c3)
    assert X.dereference(e.heap).name()== "b"
    query = Callable.build("f", [Callable.build("b"), Callable.build("a")]) 
    e.run(query)


def test_quick_unify_check():
    a = Callable.build("hallo", [NumberedVar(0), Number(10), Number(11)])
    b = Callable.build("hallo", [Callable.build("a"), Number(10), Var()])
    assert a.quick_unify_check(b)

    a = Callable.build("hallo", [NumberedVar(0), Number(10), Callable.build("b")])
    b = Callable.build("hallo", [Callable.build("a"), Number(10), Number(11)])
    assert not a.quick_unify_check(b)

    a = Callable.build("hallo", [Callable.build("a"), Number(10), Number(11)])
    b = Callable.build("hallo", [Var(), Number(10), Callable.build("b")])
    assert a.quick_unify_check(a)
    assert b.quick_unify_check(b)
    assert not a.quick_unify_check(b)

def test_copy_derefences():
    from prolog.interpreter.memo import CopyMemo
    v1 = Var()
    v1.binding = Number(10)
    v2 = v1.copy(None, CopyMemo())
    assert v2.num == 10

def test_callable_build_removes_unneeded_vars():
    h1 = Heap()
    v1 = h1.newvar()
    v1.binding = 1

    h2 = h1.branch()
    v2 = h2.newvar()
    v2.binding = 2

    t = Callable.build("hello", [v1, v2], heap=h2)
    assert t.argument_at(0) is v1
    assert t.argument_at(1) == 2

def test_cyclic_term():
    h = Heap()
    X = h.newvar()
    t = Callable.build("f", [X], heap=h)
    t.unify(X, h)

    Y = h.newvar()
    t2 = Callable.build("f", [Y], heap=h)
    t2.unify(Y, h)

    t.unify(t2, h) # does not crash
    X.unify(Y, h) # does not crash

