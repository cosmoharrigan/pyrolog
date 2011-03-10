:- module(system, [term_expand/2]).

:- use_module(list).
:- use_module(dcg).
:- use_module(numbervars).
:- use_module(structural_comparison).

term_expand(A, A) :-
	A \= (_X --> _Y).

term_expand(A, B) :-
	A = (_X --> _Y),
	trans(A, B).
