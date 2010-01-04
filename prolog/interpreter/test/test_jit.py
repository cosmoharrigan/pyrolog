from pypy.jit.metainterp.test.test_basic import LLJitMixin
from pypy.rlib.jit import OPTIMIZER_FULL

from prolog.interpreter.parsing import parse_query_term, get_engine
from prolog.interpreter.parsing import get_query_and_vars
from prolog.interpreter.continuation import jitdriver

class TestLLtype(LLJitMixin):
    def test_append(self):
        e = get_engine("""
        app([], X, X).
        app([H | T1], T2, [H | T3]) :-
            app(T1, T2, T3).
        loop(0).
        loop(X) :- X > 0, X0 is X - 1, loop(X0).
        nrev([],[]).
        nrev([X|Y],Z) :- nrev(Y,Z1),
                         app(Z1,[X],Z).

        run(X) :- solve([X]).
        solve([]).
        solve([A | T]) :-
            my_pred(A, T, T1),
            solve(T1).

        my_pred(app([], X, X), T, T).
        my_pred(app([H | T1], T2, [H | T3]), T, [app(T1, T2, T3) | T]).
        """)

        t1 = parse_query_term("app([1, 2, 3, 4, 5, 6], [8, 9], X), X == [1, 2, 3, 4, 5, 6, 8, 9].")
        t2 = parse_query_term("loop(100).")
        t3 = parse_query_term("nrev([1, 2, 3, 4, 5, 6, 7, 8, 9, 10], X), X == [10, 9, 8, 7, 6, 5, 4, 3, 2, 1].")
        t4 = parse_query_term("run(app([1, 2, 3, 4, 5, 6, 7], [8, 9], X)), X == [1, 2, 3, 4, 5, 6, 7, 8, 9].")
        def interp_w(c):
            jitdriver.set_param("inlining", True)
            if c == 0:
                t = t1
            elif c == 1:
                t = t2
            elif c == 2:
                t = t3
            elif c == 3:
                t = t4
            else:
                raise ValueError
            e.run(t)
            e.run(t)
            e.run(t)
            e.run(t)
            e.run(t)
            e.run(t)
            e.run(t)
            e.run(t)
            e.run(t)
        # XXX
        from pypy.conftest import option
        interp_w(0)
        option.view = False
        option.viewloops = True
        self.meta_interp(interp_w, [1], listcomp=True,
                         listops=True, optimizer=OPTIMIZER_FULL)
        #self.meta_interp(interp_w, [3], listcomp=True,
        #                 listops=True, optimizer=OPTIMIZER_FULL)
