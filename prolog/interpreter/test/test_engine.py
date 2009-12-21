import py
from prolog.interpreter.parsing import parse_file, TermBuilder
from prolog.interpreter.parsing import parse_query_term, get_engine
from prolog.interpreter.parsing import get_query_and_vars
from prolog.interpreter.error import UnificationFailed, CatchableError
from prolog.interpreter.test.tool import collect_all, assert_true, assert_false
from prolog.interpreter.test.tool import prolog_raises
from prolog.interpreter.engine import Heap, TrailHolder

def test_trivial():
    e = get_engine("""
        f(a).
    """)
    t, vars = get_query_and_vars("f(X).")
    e.run(t)
    assert vars['X'].dereference(e.heap).name == "a"

def test_and():
    e = get_engine("""
        g(a, a).
        g(a, b).
        g(b, c).
        f(X, Z) :- g(X, Y), g(Y, Z).
    """)
    e.run(parse_query_term("f(a, c)."))
    t, vars = get_query_and_vars("f(X, c).")
    e.run(t)
    assert vars['X'].dereference(e.heap).name == "a"

def test_and_long():
    e = get_engine("""
        f(x). f(y). f(z).
        g(a). g(b). g(c).
        h(d). h(e). h(f).
        f(X, Y, Z) :- f(X), g(Y), h(Z).
    """)
    heaps = collect_all(e, "f(X, Y, Z).")
    assert len(heaps) == 27  

def test_numeral():
    e = get_engine("""
        num(0).
        num(succ(X)) :- num(X).
        add(X, 0, X).
        add(X, succ(Y), Z) :- add(succ(X), Y, Z).
        mul(X, 0, 0).
        mul(X, succ(0), X).
        mul(X, succ(Y), Z) :- mul(X, Y, A), add(A, X, Z).
        factorial(0, succ(0)).
        factorial(succ(X), Y) :- factorial(X, Z), mul(Z, succ(X), Y).
    """)
    def nstr(n):
        if n == 0:
            return "0"
        return "succ(%s)" % nstr(n - 1)
    e.run(parse_query_term("num(0)."))
    e.run(parse_query_term("num(succ(0))."))
    t, vars = get_query_and_vars("num(X).")
    e.run(t)
    assert vars['X'].dereference(e.heap).num == 0
    e.run(parse_query_term("add(0, 0, 0)."))
    py.test.raises(UnificationFailed, e.run, parse_query_term("""
        add(0, 0, succ(0))."""))
    e.run(parse_query_term("add(succ(0), succ(0), succ(succ(0)))."))
    e.run(parse_query_term("mul(succ(0), 0, 0)."))
    e.run(parse_query_term("mul(succ(succ(0)), succ(0), succ(succ(0)))."))
    e.run(parse_query_term("mul(succ(succ(0)), succ(succ(0)), succ(succ(succ(succ(0)))))."))
    e.run(parse_query_term("factorial(0, succ(0))."))
    e.run(parse_query_term("factorial(succ(0), succ(0))."))
    e.run(parse_query_term("factorial(%s, %s)." % (nstr(5), nstr(120))))

def test_or():
    e = get_engine("""
        g(a, b).
        g(b, a).
        f(X, Y) :- g(X, b); g(a, Y).
        """)
    e.run(parse_query_term("f(a, c)."))
    e.run(parse_query_term("f(d, b)."))
    prolog_raises("ERROR", "foo(X); X = 1")


def test_or_and_call_with_cut():
    assert_false("(!, fail); true.")
    assert_true("(call(!), fail); true.")

def test_or_backtrack():
    e = get_engine("""
        a(a).
        b(b).
        g(a, b).
        g(a, a).
        f(X, Y, Z) :- (g(X, Z); g(X, Z); g(Z, Y)), a(Z).
        """)
    t, vars = get_query_and_vars("f(a, b, Z).")
    e.run(t)
    assert vars['Z'].dereference(e.heap).name == "a"
    f = collect_all(e, "X = 1; X = 2.")
    assert len(f) == 2

def test_backtrack_to_same_choice_point():
    e = get_engine("""
        a(a).
        b(b).
        start(Z) :- Z = X, f(X, b), X == b, Z == b.
        f(X, Y) :- a(Y).
        f(X, Y) :- X = a, a(Y).
        f(X, Y) :- X = b, b(Y).
    """)
    assert_true("start(Z).", e)

def test_equivalent_with_quotes():
    e = get_engine("""
        g('a', X).
        g('b', 'c').
    """)
    e.run(parse_query_term("g(a, b)."))
    e.run(parse_query_term("g(b, c)."))

def test_error_unknown_function():
    e = get_engine("""
        g(a).
        f(X) :- g(X), h(X).
    """)
    prolog_raises("existence_error(procedure, h/1)", "f(X)", e)
    
def test_collect_all():
    e = get_engine("""
        g(a).
        g(b).
        g(c).
    """)
    heaps = collect_all(e, "g(X).")
    assert len(heaps) == 3
    assert heaps[0]['X'].name == "a"
    assert heaps[1]['X'].name == "b"
    assert heaps[2]['X'].name == "c"

def test_cut():
    e = get_engine("""
        g(a).
        g(b).
        a(a).
        b(b).
        f(X) :- g(X),!,b(X).
        f(x).
        f(y).
    """)
    heaps = collect_all(e, "f(X).")
    assert len(heaps) == 0
    assert_true("!.")

def test_cut2():
    e = get_engine("""
        g(a).
        g(b).
        h(a, x).
        h(a, y).
        f(X, Y) :- g(X), !, !, !, !, !, h(X, Y).
    """)
    heaps = collect_all(e, "f(X, Y).")
    assert len(heaps) == 2

def test_cut3():
    e = get_engine("""
        member(H, [H | _]).
        member(H, [_ | T]) :- member(H, T).

        s(a, L) :- !, fail.
        s(b, L).
        s(X, L) :-
            member(Y, L),
            L = [_| S],
            s(Y, S).
    """)
    #    import pdb; pdb.set_trace()
    assert_true("s(d, [a, b]).", e)

def test_rule_with_cut_calling_rule_with_cut():
    e = get_engine("""
        f(b) :- !.
        f(c).
        g(X) :- f(X), !.
        g(a).
    """)
    heaps = collect_all(e, "g(X).")
    assert len(heaps) == 1

def test_not_with_cut():
    e = get_engine("""
    p1 :- \\+ q1.
    q1 :- fail.
    q1 :- true.
    
    p2:- \\+ q2.
    q2 :- !, fail.
    q2 :- true.
    """)
    assert_false("p1.", e)
    assert_true("p2.", e)

def test_numbers():
    e = get_engine("""
        g(1, 2).
        g(X, Y) :- g(1, X), g(1, Y).
    """)
    e.run(parse_query_term("g(2, 2)."))

def test_lists():
    e = get_engine("""
        nrev([],[]).
        nrev([X|Y],Z) :- nrev(Y,Z1),
                         append(Z1,[X],Z).

        append([],L,L).
        append([X|Y],L,[X|Z]) :- append(Y,L,Z).
    """)
    e.run(parse_query_term("append(%s, %s, X)." % (range(30), range(10))))
    return
    e.run(parse_query_term("nrev(%s, X)." % (range(15), )))
    e.run(parse_query_term("nrev(%s, %s)." % (range(8), range(7, -1, -1))))

def test_indexing():
    # this test is quite a lot faster if indexing works properly. hrmrm
    e = get_engine("g(a, b, c, d, e, f, g, h, i, j, k, l). " +
            "".join(["f(%s, g(%s)) :- g(A, B, C, D, E, F, G, H, I ,J, K, l). "
                      % (chr(i), chr(i + 1))
                                for i in range(97, 122)]))
    t = parse_query_term("f(x, g(y)).")
    for i in range(200):
        e.run(t)
    t = parse_query_term("f(x, g(y, a)).")
    for i in range(200):
        py.test.raises(UnificationFailed, e.run, t)

def test_indexing2():
    e = get_engine("""
        mother(o, j).
        mother(o, m).
        mother(o, b).

        sibling(X, Y) :- mother(Z, X), mother(Z, Y).
    """)
    heaps = collect_all(e, "sibling(m, X).")
    assert len(heaps) == 3

def test_runstring():
    e = get_engine("foo(a, c).")
    e.runstring("""
        :- op(450, xfy, foo).
        a foo b.
        b foo X :- a foo X.
    """)
    assert_true("foo(a, b).", e)

def test_handle_non_callable():
    py.test.raises(CatchableError, assert_true, "1.")

def test_call_atom():
    e = get_engine("""
        test(a).
        test :- test(_).
    """)
    assert_true("test.", e)


def test_metainterp():
    e = get_engine("""
        run(X) :- solve([X]).
        solve([]).
        solve([A | T]) :-
            my_pred(A, T, T1),
            solve(T1).

        my_pred(app([], X, X), T, T).
        my_pred(app([H | T1], T2, [H | T3]), T, [app(T1, T2, T3) | T]).

    """)
    assert_true("run(app([1, 2, 3, 4], [5, 6], X)), X == [1, 2, 3, 4, 5, 6].", e)

class TestHeap(object):
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
