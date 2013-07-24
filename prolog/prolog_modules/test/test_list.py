from prolog.interpreter.continuation import Engine
from prolog.interpreter.test.tool import collect_all, assert_false, assert_true

e = Engine(load_system=True)
def test_member():
    assert_true("member(1, [1,2,3]).", e)

def test_not_member():
    assert_false("member(666, [661,662,667,689]).", e)

def test_not_member_of_empty():
    assert_false("member(666, []).", e)

def test_all_members():
    data = [ 2**x for x in range(30) ]
    heaps = collect_all(e, "member(X, %s)." % (str(data)))
    nums = [ h["X"].num for h in heaps ]
    assert nums == data

def test_select():
    assert_true("select(1, [1, 2, 3, 1], [2, 3, 1]).", e)
    assert_true("select(1, [1, 2, 3, 1], [1, 2, 3]).", e)
    assert_false("select(1, [1, 2, 3, 1], [1, 2, 3, 1]).", e)
    assert_false("select(1, [1, 2, 3, 1], [2, 3]).", e)
    assert_false("select(2, [], []).", e)
    assert_false("select(2, [], [X]).", e)

def test_nextto():
    assert_true("nextto(666, 1024, [1, 2, 3, 4, 666, 1024, 8, 8, 8]).", e)
    assert_false("nextto(8, 4, [1, 2, 3, 4, 666, 1024, 8, 8, 8]).", e)
    assert_false("nextto(1, 2, [2, 1]).", e)

def test_memberchk():
    assert_true("memberchk(432, [1, 2, 432, 432, 1]).", e)
    assert_false("memberchk(0, [1, 2, 432, 432, 1]).", e)

def test_subtract():
    assert_true("subtract([1, 2, 3, 4], [2], [1, 3, 4]).", e)
    assert_true("subtract([a, c, d], [b], [a, c, d]).", e)
    assert_true("subtract([a, b, c], [], [a, b, c]).", e)
    assert_true("subtract([1, 1, 6], [1, 6], []).", e)
