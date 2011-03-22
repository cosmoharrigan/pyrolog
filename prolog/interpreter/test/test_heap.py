from prolog.interpreter.heap import Heap
from prolog.interpreter.term import AttVar, Var, Callable, Number

def test_heap():
    h1 = Heap()
    v1 = h1.newvar()
    v2 = h1.newvar()
    h1.add_trail(v1)
    v1.binding = 1
    h2 = h1.branch()
    h2.add_trail(v1)
    v1.binding = 2
    h2.add_trail(v2)
    v2.binding = 3

    h3 = h2.revert_upto(h1)
    assert v1.binding == 1
    assert v2.binding is None
    assert h3 is h2

    h1 = Heap()
    h2 = h1.revert_upto(h1)
    assert h2 is h1

    h1 = Heap()
    h2 = h1.branch()
    h3 = h2.revert_upto(h1, discard_choicepoint=True)
    assert h3 is h1

def test_heap_dont_trail_new():
    h1 = Heap()
    v1 = h1.newvar()
    h1.add_trail(v1)
    v1.binding = 1
    h2 = h1.branch()
    v2 = h2.newvar()
    h2.add_trail(v1)
    v1.binding = 2
    h2.add_trail(v2)
    v2.binding = 3

    h3 = h2.revert_upto(h1)
    assert v1.binding == 1
    assert v2.binding == 3 # wasn't undone, because v2 dies
    assert h3 is h2

def test_heap_discard():
    h1 = Heap()
    h2 = h1.branch()
    h3 = h2.branch()
    h = h2.discard(h3)
    assert h3.prev is h1
    assert h3 is h

    h0 = Heap()
    v0 = h0.newvar()

    h1 = h0.branch()
    v1 = h1.newvar()

    h2 = h1.branch()
    v2 = h2.newvar()

    h2.add_trail(v0)
    v0.binding = 1
    h2.add_trail(v1)
    v1.binding = 2

    h3 = h2.branch()
    h3.add_trail(v2)
    v2.binding = 3

    h = h2.discard(h3)
    assert h3.prev is h1
    assert h3 is h

    assert h3.revert_upto(h0)
    assert v0.binding is None
    assert v1.binding is None
    assert v2.binding == 3 # not backtracked, because it goes away

def test_heap_discard_variable_shunting():
    h0 = Heap()
    v0 = h0.newvar()

    h1 = h0.branch()
    v1a = h1.newvar()
    v1b = h1.newvar()

    h2 = h1.branch()
    v2 = h1.newvar()

    h2.add_trail(v0)
    v0.binding = 1
    h2.add_trail(v1a)
    v1a.binding = 2

    h = h1.discard(h2)
    assert h2.prev is h0
    assert h2 is h
    assert h1.discarded
    assert h1.prev is h2                                                                                                                                

    h2.add_trail(v1b)
    v1b.binding = 3

    assert h2.revert_upto(h0)

    assert v0.binding is None
    assert v1a.binding == 2 # not backtracked, because it goes away
    assert v1b.binding == 3 # not backtracked, because it goes away

def test_new_attvar():
    h = Heap()
    v = h.new_attvar()
    assert isinstance(v, AttVar)
    assert v.created_after_choice_point is h

def test_add_trail_atts():
    h1 = Heap()
    va = h1.new_attvar()
    vb = h1.new_attvar()
    va.atts = {"m": 17}

    h2 = h1.branch() 
    h2.add_trail_atts(va, "m")
    va.atts["m"] = 45
    h2.add_trail_atts(vb, "m")
    vb.atts["m"] = 39

    h3 = h2.revert_upto(h1)
    assert h3 is h2
    assert va.atts["m"] == 17
    assert vb.atts == {}

def test_heap_dont_trail_new_att_vars():
    h1 = Heap()
    v1 = h1.new_attvar()
    h1.add_trail_atts(v1, "m")
    v1.atts["m"] = 1
    h2 = h1.branch()
    v2 = h2.new_attvar()
    h2.add_trail_atts(v1, "m")
    v1.atts["m"] = 2
    h2.add_trail_atts(v2, "m")
    v2.atts["m"] = 3

    h3 = h2.revert_upto(h1)
    assert v1.atts["m"] == 1
    assert v2.atts["m"] == 3 # wasn't undone, because v2 dies
    assert h3 is h2
    
def test_discard_with_attvars():
    h0 = Heap()
    v0 = h0.new_attvar()

    h1 = h0.branch()
    v1 = h1.new_attvar()

    h2 = h1.branch()
    v2 = h2.new_attvar()

    h2.add_trail_atts(v0, "m")
    v0.atts = {"m": 1}
    h2.add_trail_atts(v1, "n")
    v1.atts = {"n": 2}

    h3 = h2.branch()
    h3.add_trail_atts(v2, "a")
    v2.atts = {"a": 3}

    h = h2.discard(h3)
    assert h3.prev is h1
    assert h3 is h
    assert h3.revert_upto(h0)
    assert v0.atts == {}
    assert v1.atts == {}
    assert v2.atts == {"a": 3}

def xtest_simple_hooks():
    hp = Heap()
    v = Var()
    a = AttVar()
    a.atts["m"] = 1
    v.unify(a, hp)
    assert len(hp.hooks) == 0
    v.unify(Number(1), hp)
    assert hp.hooks == [a]

    hp = Heap()
    v1 = Var()
    v2 = Var()
    a1 = AttVar()
    a2 = AttVar()
    v1.unify(a1, hp)
    assert hp.hooks == []
    v2.unify(a2, hp)
    assert hp.hooks == []
    v1.unify(v2, hp)
    assert hp.hooks == [a2]

    hp = Heap()
    v1 = Var()
    v2 = Var()
    v3 = Var()
    a1 = AttVar()
    a2 = AttVar()
    a3 = AttVar()
    v1.unify(a1, hp)
    v2.unify(a2, hp)
    v3.unify(a3, hp)
    v1.unify(v2, hp)
    v2.unify(v3, hp)
    assert hp.hooks == [a2, a3]

    hp = Heap()
    v1 = Var()
    v2 = Var()
    a1 = AttVar()
    a2 = AttVar()
    v1.unify(a1, hp)
    v2.unify(a2, hp)
    assert hp.hooks == []
    v1.unify(v2, hp)
    assert hp.hooks == [a2]
    v1.unify(Number(1), hp)
    assert hp.hooks == [a2, a1]

def xtest_number_of_hooks():
    hp = Heap()
    v = Var()
    av = AttVar()
    v.unify(av, hp)
    assert hp.hooks == []
    a = Callable.build('a')
    v.unify(a, hp)
    assert hp.hooks == [av]
    v.unify(a, hp)
    assert hp.hooks == [av]
