:- module(dcg, [trans/2]).
:- use_module('../../prolog_modules/list').

trans((H --> B), (TransH :- TransB)) :-
	add_arguments(H, X0, X1, TransH),
	trans_body(B, X0, X1, false, _, TransB).

add_arguments(H, X0, X1, F) :-
	H =.. List, !,
	append(List, [X0, X1], Args),
	F =.. Args. 

trans_body((B1, B2), X0, XE, EmitIn, EmitOut, R) :-
	trans_body_call(B1, X0, X1, EmitIn, Emit, R1),
	trans_body(B2, X1, XE, Emit, EmitOut, R2),
	append_bodies(R1, R2, R).

trans_body(X, X0, XE, EmitIn, EmitOut, R) :-
	X \= (_, _),
	trans_body_call(X, X0, XE, EmitIn, EmitOut, R).

trans_body_call(X, X0, XE, true, false, X0 = L) :-
	is_list(X),
	append(X, XE, L).

trans_body_call(X, X0, XE, false, false, true) :-
	is_list(X),
	append(X, XE, X0).

trans_body_call(A, X0, XE, _, true, R) :-
	callable(A),
	\+ is_list(A),
	add_arguments(A, X0, XE, R).

append_bodies(true, B, B).
append_bodies(B, true, B) :-
	B \= true.
append_bodies(B1, B2, (B1, B2)) :-
	B1 \= true.

/*
trans_body({C1, C2}, X0, XE, (C1, R)) :-
	trans_body({C2}, X0, XE, R), !.

trans_body({C}, X0, XE, (C, X0=XE)) :- !.
*/
