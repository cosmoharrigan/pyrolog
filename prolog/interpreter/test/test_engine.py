import py
from prolog.interpreter.parsing import parse_file, TermBuilder
from prolog.interpreter.parsing import parse_query_term, get_engine
from prolog.interpreter.parsing import get_query_and_vars
from prolog.interpreter.error import UnificationFailed, CatchableError
from prolog.interpreter.test.tool import collect_all, assert_true, assert_false
from prolog.interpreter.test.tool import prolog_raises
from prolog.interpreter.engine import Heap, TrailHolder

def test_error_unknown_function():
    e = get_engine("""
        g(a).
        f(X) :- g(X), h(X).
    """)
    prolog_raises("existence_error(procedure, h/1)", "f(X)", e)
    

def test_numbers():
    e = get_engine("""
        g(1, 2).
        g(X, Y) :- g(1, X), g(1, Y).
    """)
    e.run(parse_query_term("g(2, 2)."))

def test_handle_non_callable():
    prolog_raises('type_error(callable,1)', "1")


class XTestHeap(object):
    def test_trail(self):
        h = Heap()
        t1 = h.newtrail()
        assert t1.last_choice() is None
        t2 = h.newtrail()
        t3 = h.newtrail()
        t3.is_choice = True
        t4 = h.newtrail()
        t5 = h.newtrail()
        assert t3.last_choice() is t3
        assert t4.last_choice() is t3
        assert t5.last_choice() is t3

    def test_revert(self):
        class FakeVar(object):
            binding = None
            created_after_choice_point = None
        X = FakeVar()
        Y = FakeVar()
        h = Heap()
        h.add_trail(X)
        X.binding = 1
        state = h.branch()
        h.add_trail(Y)
        Y.binding = 2
        h.revert(state)
        assert Y.binding is None
        assert X.binding == 1
        h.newtrail()
        h.newtrail()
        h.add_trail(Y)
        Y.binding = 3
        h.revert(state)
        assert Y.binding is None
        assert X.binding == 1

    def test_dont_trail(self):
        class FakeVar(object):
            def __init__(self, trail):
                self.binding = None
                self.created_after_choice_point = trail

        h = Heap()
        state = h.branch()
        X = FakeVar(state)
        Y = FakeVar(state)
        h.add_trail(X)
        X.binding = 1
        h.add_trail(Y)
        Y.binding = 2
        h.revert(state)
        # the bindings of X and Y were not undone, since a trace wasn't even
        # necessary
        assert X.binding == 1
        assert Y.binding == 2

    def test_dont_trail_discard(self):
        class FakeVar(object):
            def __init__(self, trail):
                self.binding = None
                self.created_after_choice_point = trail

        h = Heap()
        state = h.branch()
        X = FakeVar(state)
        Y = FakeVar(state)
        h.add_trail(X)
        X.binding = 1
        state2 = h.branch()
        Z = FakeVar(state2)
        h.discard(state2)
        h.add_trail(Y)
        Y.binding = 2
        h.add_trail(Z)
        Z.binding = 3
        h.revert(state)
        # the bindings were not undone, since a trace wasn't even necessary
        assert X.binding == 1
        assert Y.binding == 2
        assert Z.binding == 3

    def test_discard(self):
        h = Heap()
        t1 = h.newtrail()
        t2 = h.newtrail()
        state = h.branch()
        t3 = h.newtrail()
        t4 = h.newtrail()
        h.discard(state)
        assert h.current is t2
