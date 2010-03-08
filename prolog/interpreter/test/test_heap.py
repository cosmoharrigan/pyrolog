from prolog.interpreter.heap import Heap

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


