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
	trans_body_call(B1, X0, X1, EmitIn, Emit, false, R1),
	trans_body(B2, X1, XE, Emit, EmitOut, R2),
	append_bodies(R1, R2, R).

trans_body(X, X0, XE, EmitIn, EmitOut, R) :-
	X \= (_, _),
	trans_body_call(X, X0, XE, EmitIn, EmitOut, true, R).

trans_body_call(X, X0, XE, Emit, false, _, R) :-
	is_list(X),
	append(X, XE, L),
	(Emit = true ->
		R = (X0 = L)
	;
		R = true,
		X0 = L
	).

trans_body_call(A, X0, XE, _, true, _, R) :-
	callable(A),
	\+ functor(A, {}, _),
	\+ is_list(A),
	add_arguments(A, X0, XE, R).

trans_body_call({X}, X0, XE, _, _, Emit, R) :-
	trans_braces(X, X0, XE, Emit, R).

append_bodies(true, B, B).

append_bodies(B, true, B) :-
	B \= true.

append_bodies(B1, B2, (B1, B2)) :-
	B1 \= true.

trans_braces(X, X0, XE, true, (X, X0=XE)) :-
	X \= (_, _).

trans_braces(X, _, _, false, X) :-
	X \= (_, _).

trans_braces((B1, B2), X0, XE, Emit, (R1, R2)) :-
	trans_braces(B1, X0, XE, false, R1),
	trans_braces(B2, X0, XE, Emit, R2).
