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
