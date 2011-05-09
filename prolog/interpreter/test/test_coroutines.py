import py
from prolog.interpreter.test.tool import assert_true, assert_false, \
prolog_raises
from prolog.interpreter.continuation import Engine
from prolog.interpreter.parsing import get_engine

e = get_engine("""
    f(a).
    z :- call(f(a)).
    :- assert(m:g(q)).

    test_once(X) :-
        var(X), 
        X = 1.
    """,
    load_system=True)

def test_freeze():
    assert_true("freeze(X, Y = 1), X = 1, Y == 1.", e)
    assert_false("freeze(X, true), X = 1, attvar(X).", e)
    assert_false("freeze(X, Y = 1), X = 1, fail; Y == 1.", e)
    assert_true("freeze(a, Y = 1), Y == 1.", e)
    prolog_raises("existence_error(_, _)", "freeze(a, a)", e)
    assert_true("freeze(X, Y = 1), freeze(X, Z = 2), X = a, Y == 1, Z == 2.", e)
    assert_true("freeze(X, f(a)), X = 1.", e)
    assert_true("freeze(X, user:f(a)), X = 1.", e)
    assert_true("freeze(X, m:g(q)), X = 1.", e)
    assert_false("freeze(X, Y = 1), freeze(X, Y = 2), X = a.", e)
    assert_true("freeze(X, Y = 1), freeze(X, Z = 2), X = a, Y == 1, Z == 2.", e)
    assert_true("freeze(X, Z1 = 1), freeze(Y, Z2 = 2), var(Z1), var(Z2), X = Y, var(Z1), var(Z2).", e)
    assert_true("freeze(X, Z1 = 1), freeze(Y, Z2 = 2), var(Z1), var(Z2), X = Y, var(Z1), var(Z2), X = 1, Z1 == 1, Z2 == 2.", e)
    assert_true("freeze(X, Z1 = 1), freeze(Y, Z2 = 2), var(Z1), var(Z2), X = Y, var(Z1), var(Z2), Y = 1, Z1 == 1, Z2 == 2.", e)

def test_frozen():
    assert_false("frozen(a, a).", e)
    assert_true("frozen(1, X), X == true.", e)
    assert_true("frozen(X, X), X == true.", e)
    assert_true("frozen(X, Y), Y == true, var(X).", e)
    assert_true("freeze(X, f(a)), frozen(X, user:f(a)).", e)
    assert_true("freeze(X, m:g(q)), frozen(X, R), R == m:g(q).", e)
    assert_true("freeze(X, true), frozen(X, user:true), freeze(X, fail), frozen(X, (user:true, user:fail)).", e)
    assert_true("freeze(X, true), X = a, frozen(X, R), R == true.", e)

def test_when():
    assert_true("when(nonvar(X), Y = 1), X = a, Y == 1.", e)
    assert_true("when(nonvar(a), f(a)).", e)
    assert_true("when(nonvar(a), (X = 1, Y = 2)), X == 1, Y == 2.", e)
    assert_true("when(nonvar(a), z).", e)
    assert_true("when(nonvar(X), f(a)), X = 1.", e)
    assert_true("when(ground(f(X, Y)), Z = 1), X = 1, var(Z), Y = a, Z == 1.", e)
    assert_true("when(ground(f(X, Y)), Z = 1), Y = 1, var(Z), X = a, Z == 1.", e)
    assert_false("when(ground(f(X, Y)), Z = 1), X = 1, Z == 1.", e)
    assert_true("when((ground(X), ground(Y)), Z = 1), X = a, var(Z), Y = b, Z == 1.", e)
    assert_true("when((ground(X), ground(Y)), Z = 1), Y = a, var(Z), X = b, Z == 1.", e)
    assert_true("when((ground(a), ground(Y)), Z = 1), var(Z), Y = a, Z == 1.", e)
    assert_true("when((ground(X), ground(a)), Z = 1), var(Z), X = a, Z == 1.", e)
    assert_true("when((ground(a), ground(a)), Z = 1), Z == 1.", e)
    assert_true("when((ground(X); ground(Y)), Z = 1), var(Z), Y = b, Z == 1.", e)
    assert_true("when((ground(X); ground(Y)), Z = 1), var(Z), X = b, Z == 1.", e)
    assert_true("when((ground(X); ground(Y)), Z = 1), var(Z), Y = b, Z == 1, X = a.", e)
    assert_true("when((ground(X); ground(Y)), test_once(Z)), var(Z), Y = b, Z == 1, X = a.", e)
    assert_true("when(?=(1, 1), X = a), X == a.", e)
    assert_true("when(?=(X, X), Z = a), Z == a.", e)
    assert_false("when(?=(X, Y), Z = a), Z == a.", e)
    assert_true("when(?=(X, Y), Z = a), Y = a, X = b, Z == a.", e)
    assert_true("when(?=(X, Y), Z = a), X = a, Y = b, Z == a.", e)
    assert_true("when(?=(f(A, B), f(a, b)), test_once(Z)), var(Z), A = 1, B = 2, Z == 1.", e)

    #assert_false("when(?=(f(1), f(2)), nl), fail.", e) # minimal example for cut bug
    #assert_false("when(?=(f(A, B), f(a, b)), test_once(Z)), var(Z), A = 1, B = 2, Z == a.", e)

    assert_true("when(?=(f(X), f(X)), Z = a), Z == a.", e)
    assert_true("when(?=(f(X, Y), f(X, Y)), Z = a), Z == a.", e)
    assert_true("when(?=(f(X, Y), f(X, W)), Z = a), var(Z), Y = 1, var(Z), W = 1, Z == a.", e)
    assert_false("when(?=(f(X), f(Y)), Z = a), Z == a.", e)
    assert_false("when(?=(X, f(X)), Z = a), Z == a.", e)
    prolog_raises("instantiation_error", "when(X, X == 1)", e)
    prolog_raises("instantiation_error", "when(nonvar(a), X)", e)
    assert_true("when(ground(1), m:g(q)).", e)
    assert_true("when(ground(X), Y = 1), X = a, Y == 1.", e)
    assert_true("when(ground(X), Y = 1), when(ground(X), Z = 2), X = a, Y == 1, Z == 2.", e)
    assert_true("when(ground(X), Y), when(ground(A), Y = (B = 3)), A = a, X = q, Y == (3 = 3).", e)
    prolog_raises("instantiation_error", "when(ground(X), Y), when(ground(A), Y = (B = 3)), X = q, A = 1", e)
    assert_true("when(ground(f(X, Y)), when(ground(X), Z = 1)), X = a, var(Z), Y = b, Z == 1.", e)
    assert_true("when(ground(f(X, Y)), when(ground(A), Z = 1)), X = a, var(Z), Y = b, var(Z), A = 1, Z == 1.", e)
    prolog_raises("domain_error(_, _)", "when(var(X), f(a))", e)
    prolog_raises("domain_error(_, _)", "when((ground(1), (ground(1), var(1))), f(a))", e)
    prolog_raises("domain_error(_, _)", "when(((1; 2), (ground(1), nonvar(1))), f(a))", e)

    assert_true("when(?=(f(X, Y), f(A, B)), Q = 1), X = a, A = a, var(Q), Y = b, B = b, Q == 1.", e)
    assert_true("when(?=(f(X, Y), f(A, B)), Q = 1), Y = a, B = a, var(Q), X = b, A = b, Q == 1.", e)
    assert_true("when(?=(f(X, Y), f(A, B)), Q = 1), Y = a, B = 1, Q == 1.", e)
    assert_true("when(?=(f(X, Y), f(A, B)), Q = 1), X = a, A = 1, Q == 1.", e)
    assert_true("when(?=(f(X, Y), f(A, B)), Q = 1), X = a, B = 1, var(Q).", e)

def test_hard_when():
    assert_true("findall(Z, (when(?=(X, Y), Z = a), X = a, Y = b), L), L == [a].", e)
    assert_true("when(nonvar(X), Y = 1), when(nonvar(A), G = 1), X = A, var(Y), var(G).", e)
    assert_true("when(nonvar(X), A = 1), when(nonvar(Y), B = 2), X = Y, Y = a, A == 1, B == 2.", e)
    assert_true("when(nonvar(X), assert(xyz(a))), when(nonvar(Y), assert(xyz(b))), X = Y, Y = a.", e)
    assert_true("findall(X, xyz(X), L), L == [b, a].", e)
    assert_true("abolish(xyz/1).", e)

def test_meta_predicate_with_when():
    e = get_engine("""
    :- use_module(m).
    """,
    m = """
    :- module(m, [f/2]).

    f(X, Y) :-
        when(nonvar(X), Y == X).
    """, 
    load_system=True)
    assert_true("module(m).", e)
    assert_true("f(X, a), X = a.", e)
    assert_false("f(X, a), X = b.", e)
    assert_true("module(user).", e)
    assert_true("f(X, a), X = a.", e)
    assert_false("f(X, a), X = b.", e)
    assert_true("m:f(X, a), X = a.", e)
    assert_false("m:f(X, a), X = b.", e)

def test_block():
    e = get_engine("""
    :- block f('?', '-', '?'), f('-', '-', '?').
    :- block g('?').
    :- block h('-', '-', '-', '?'), h('-', '-', '?', '?'), h('-', '?', '?', '?').

    f(A, B, C) :-
        C = 10.

    g(_) :-
        assert(gg(1)).

    h(A, B, C, D) :-
        D is A + B + C.
    """, load_system=True)
    assert_false("f(X, Y, Z), Z == 10.", e)
    assert_false("f(a, X, Z), Z == 10.", e)
    assert_true("f(a, b, Z), Z == 10.", e)
    assert_true("f(a, X, Z), \+ Z == 10, X = 5, Z == 10.", e)
    assert_true("f(A, B, Z), \+ Z == 10, A = a, \+ Z == 10, B = b, Z == 10.", e)
    #assert_true("f(a, X, Z), (X = 1, fail; true), var(Z).", e)

    prolog_raises("existence_error(_, _)", "g(5), gg(1)", e)
    prolog_raises("existence_error(_, _)", "g(X), gg(1)", e)

    assert_true("h(A, B, C, D), var(D), C = 5, var(D), B = 5, var(D), A = 5, D == 15.", e)
    prolog_raises("instantiation_error", "h(5, B, C, D)", e)
    prolog_raises("instantiation_error", "h(5, 1, C, D)", e)
    assert_true("h(1, 2, 3, 6).", e)
    assert_true("h(A, B, C, D), var(D), B = 5, var(D), C = 5, var(D), A = 5, D == 15.", e)

def test_sudoku_with_when():
    e = get_engine("""
    len(List, R) :-
        len(List, 0, R).

    len([], A, A).
    len([_|T], A, R) :-
        A1 is A + 1,
        len(T, A1, R).

    mem(X, [X|_]).
    mem(X, [_|T]) :-
        mem(X, T).

    rem(_, [], []).
    rem(X, [X|T], T).
    rem(X, [H|T], [H|R]) :-
        X \= H,
        rem(X, T, R).

    perm([], []).
    perm(L, [X|R]) :-
        mem(X, L),
        rem(X, L, L2),
        perm(L2, R).

    set_list_constraints([]).
    set_list_constraints([H|T]) :-
        set_element_constrains(H, T),
        set_list_constraints(T).

    set_element_constrains(_, []).
    set_element_constrains(X, [H|T]) :-
        when((ground(X), ground(H)), X \== H),
        set_element_constrains(X, T).

    set_row_contraints([]).
    set_row_contraints([H|T]) :-
        set_list_constraints(H),
        set_row_contraints(T).

    set_col_constraints([[], [], [], []]).
    set_col_constraints([[H1|T1], [H2|T2], [H3|T3], [H4|T4]]) :-
        set_list_constraints([H1, H2, H3, H4]),
        set_col_constraints([T1, T2, T3, T4]).

    set_box_constraints([[A1, A2, A3, A4],
                         [B1, B2, B3, B4],
                         [C1, C2, C3, C4],
                         [D1, D2, D3, D4]]) :-

        set_list_constraints([A1, A2, B1, B2]),
        set_list_constraints([C1, C2, D1, D2]),
        set_list_constraints([A3, A4, B3, B4]),
        set_list_constraints([C3, C4, D3, D4]).
        
    init([]).
    init([H|T]) :-
        perm([1, 2, 3, 4], H),
        init(T).

    sudoku(S) :-
        S = [[A1, A2, A3, A4],
             [B1, B2, B3, B4],
             [C1, C2, C3, C4],
             [D1, D2, D3, D4]],

        set_row_contraints(S),
        set_col_constraints(S),
        set_box_constraints(S),
        init(S).
    """, load_system=True)

    assert_true("sudoku([[1, 2, 3, 4], [3, 4, 1, 2], [2, 1, 4, 3], [4, 3, 2, 1]]).", e)
    assert_true("sudoku([[2, 1, 4, 3], [3, 4, 2, 1], [4, 3, 1, 2], [1, 2, 3, 4]]).", e)
    assert_true("sudoku([[3, 1, 2, 4], [2, 4, 3, 1], [4, 3, 1, 2], [1, 2, 4, 3]]).", e)
    assert_true("sudoku([[3, 4, 2, 1], [1, 2, 3, 4], [2, 1, 4, 3], [4, 3, 1, 2]]).", e)
    assert_true("sudoku([[4, 2, 3, 1], [1, 3, 4, 2], [2, 4, 1, 3], [3, 1, 2, 4]]).", e)

    assert_false("sudoku([[3, 4, 2, 1], [1, 2, 3, 4], [2, 1, 4, 3], [1, 3, 1, 2]]).", e)
    assert_false("sudoku([[4, 2, 3, 1], [2, 3, 4, 1], [2, 4, 1, 3], [3, 1, 2, 4]]).", e)

def test_sat_solver():
    e = get_engine("""
    sat(Clauses, Vars) :-
        problem_setup(Clauses),
        elim_var(Vars).

    elim_var([]).
    elim_var([Var | Vars]) :-
        elim_var(Vars),
        (Var = true ; Var = false).

    problem_setup([]).
    problem_setup([Clause | Clauses]) :-
        clause_setup(Clause),
        problem_setup(Clauses).

    clause_setup([Pol-Var | Pairs]) :-
        set_watch(Pairs, Var, Pol).

    set_watch([], Var, Pol) :-
        Var = Pol.
    set_watch([Pol2-Var2 | Pairs], Var1, Pol1) :-
        watch(Var1, Pol1, Var2, Pol2, Pairs).

    :- block watch('-', '?', '-', '?', '?').

    %:- assert((watch(G568, G581, G584, G597, G600):- (var(G568), var(G584), true), !, when((nonvar(G568);nonvar(G584);nonvar(_G603)), watch(G568, G581, G584, G597, G600)))).
    

    watch(Var1, Pol1, Var2, Pol2, Pairs) :-
        nonvar(Var1)
         ->	update_watch(Var1, Pol1, Var2, Pol2, Pairs)
         ;	update_watch(Var2, Pol2, Var1, Pol1, Pairs).

    update_watch(Var1, Pol1, Var2, Pol2, Pairs) :-
        Var1 == Pol1
         ->	true
         ;	set_watch(Pairs, Var2, Pol2).
    """,
    load_system=True)

    assert_true("sat([[false-X]], [X]), X == false.", e)
    assert_true("sat([[true-X], [false-Y]], [X, Y]), X == true, Y == false.", e)
    #assert_true("findall(X, sat([[true-X, false-Y]], [X, Y]), L), L == [true, true, false].", e)
    assert_false("sat([[true-X], [true-Y], [true-Z], [false-Z]], [X, Y, Z]).", e)
    #assert_false("sat([[true-X, false-Y], [true-Y], [true-X], [false-Y]], [X, Y, Z]).", e)
    assert_false("sat([[true-X], [false-X]], [X]).", e)
