import py
from prolog.interpreter.error import UnificationFailed
from prolog.interpreter.term import Atom, Var, Number, Term, BlackBox
from prolog.interpreter.term import NumberedVar
from prolog.interpreter.continuation import Heap, Engine

def test_atom():
    a = Atom.newatom("hallo")
    b = Atom.newatom("hallo")
    # does not raise
    a.unify(b, None)
    py.test.raises(UnificationFailed, "a.unify(Atom.newatom('xxx'), None)")

def test_var():
    b = Var()
    heap = Heap()
    b.unify(Atom.newatom("hallo"), heap)
    assert b.getvalue(heap).name == "hallo"
    a = Var()
    b = Var()
    a.unify(b, heap)
    a.unify(Atom.newatom("hallo"), heap)
    assert a.getvalue(heap).name == "hallo"
    assert b.getvalue(heap).name == "hallo"

def test_unify_var():
    b = Var()
    heap = Heap()
    b.unify(b, heap)
    b.unify(Atom.newatom("hallo"), heap)
    py.test.raises(UnificationFailed, b.unify, Atom.newatom("bye"), heap)

def test_recursive():
    b = Var()
    heap = Heap()
    b.unify(Term("hallo", [b]), heap)

def test_term():
    X = Var()
    Y = Var()
    t1 = Term("f", [Atom.newatom("hallo"), X])
    t2 = Term("f", [Y, Atom.newatom("HALLO")])
    heap = Heap()
    print t1, t2
    t1.unify(t2, heap)
    assert X.getvalue(heap).name == "HALLO"
    assert Y.getvalue(heap).name == "hallo"

def test_blackbox():
    bl1 = BlackBox()
    bl2 = BlackBox()
    heap = Heap()
    bl1.unify(bl1, heap)
    py.test.raises(UnificationFailed, bl1.unify, bl2, heap)

def test_enumerate_vars():
    X = Var()
    Y = Var()
    t1 = Term("f", [X, X, Term("g", [Y, X])])
    t2 = t1.enumerate_vars({})
    assert isinstance(t2, Term)
    assert t2.signature == t1.signature
    assert t2.argument_at(0) is t2.argument_at(1)
    assert t2.argument_at(0).num == 0
    assert t2.argument_at(2).argument_at(1).num == 0

def test_copy_and_unify():
    heap = Heap()
    X = Var()
    Y = Var()
    Z = NumberedVar(0)
    t1 = Term("f", [Z, Term("g", [Z, Atom.newatom("h")]), Z])
    t2 = Term("f", [Atom.newatom("i"), X, Y])
    env = [None]
    t1.unify_and_standardize_apart(t2, heap, env)

def test_run():
    e = Engine()
    e.add_rule(Term("f", [Atom.newatom("a"), Atom.newatom("b")]))
    X = Var()
    Y = Var()
    e.add_rule(Term("f", [X, X]))
    e.add_rule(Term(":-", [Term("f", [X, Y]),
                           Term("f", [Y, X])]))
    X = e.heap.newvar()
    e.run(Term("f", [Atom.newatom("b"), X]))
    assert X.dereference(e.heap).name == "b"
    query = Term("f", [Atom.newatom("b"), Atom.newatom("a")]) 
    e.run(query)
