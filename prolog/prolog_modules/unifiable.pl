:- module(unifiable, [unifiable/3]).

unifiable(A, B, List) :-
	unifiable(A, B, [], List).

unifiable(A, B, Acc, [A-B|Acc]) :-
	var(A),
	var(B),
	A \== B.

unifiable(A, B, Acc, Acc) :-
	var(A),
	var(B),
	A == B.

unifiable(A, B, Acc, [A-B|Acc]) :-
	var(A),
	nonvar(B).

unifiable(A, B, Acc, [B-A|Acc]) :-
	var(B),
	nonvar(A).

unifiable(A, B, Acc, List) :-
	nonvar(A),
	nonvar(B),
	functor(A, Functor, Arity),
	functor(B, Functor, Arity),
	A =.. [_|ArgsA],
	B =.. [_|ArgsB],
	unifiable_list(ArgsA, ArgsB, Acc, List).

unifiable_list([], [], Acc, Acc).
unifiable_list([A|RestA], [B|RestB], Acc, List) :-
	unifiable(A, B, Acc, NewAcc),
	unifiable_list(RestA, RestB, NewAcc, List).
