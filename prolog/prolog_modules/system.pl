:- module(system, [term_expand/2]).

:- use_module(list).
:- use_module(dcg).

term_expand(A, A) :-
	A \= (_X --> _Y).

term_expand(A, B) :-
	A = (_X --> _Y),
	trans(A, B).

expand_and_assert(Rule) :-
	term_expand(Rule, Modified),
	assert(Modified).
