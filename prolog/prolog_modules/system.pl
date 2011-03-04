:- module(system, [term_expand/2]).

:- use_module(list).
:- use_module(dcg).

term_expand(A, A) :-
	A \= (_X --> _Y),
	assert(A).

term_expand(A, B) :-
	A = (_X --> _Y),
	trans(A, B),
	assert(B).
