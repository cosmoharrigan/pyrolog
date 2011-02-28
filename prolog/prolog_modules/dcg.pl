:- module(dcg, [trans/2]).
:- use_module('../../prolog_modules/list').

trans((H --> B), (TransH :- TransB)) :-
	trans_head(H, X0, X1, TransH),
	trans_body(B, X0, X1, TransB).

trans_head(H, X0, X1, F) :-
	atom(H), !,
	F =.. [H, X0, X1].

trans_head(H, X0, X1, F) :-
	H =.. List, !,
	append(List, [X0, X1], Args),
	F =.. Args. 

trans_body((B1, B2), X0, XE, XTemp = R) :-
	is_list(B1),
	is_list(B2), !,
	append(B1, XTemp, X0),
	append(B2, XE, R).

trans_body((B1, B2), X0, XE, F2) :-
	is_list(B1), !,
	append(B1, XTemp, X0),
	trans_body(B2, XTemp, XE, F2).

trans_body((B1, B2), X0, XE, (F1, XTemp = R)) :-
	is_list(B2), !,
	trans_body(B1, X0, XTemp, F1),
	append(B2, XE, R).

trans_body((B1, B2), X0, XE, (F1, F2)) :-
	trans_body(B1, X0, XTemp, F1),
	trans_body(B2, XTemp, XE, F2), !.

trans_body(B, X0, XE, F) :-
	atom(B), !,
	F =.. [B, X0, XE].

trans_body(B, X0, XE, true) :-
	is_list(B),
	append(B, XE, R),
	X0 = R, !.
/*
trans_body(B, X0, XE, F) :-
	B =.. [Functor|Args],
	Functor \= {}, !,
	append(Args, [X0], Args1),
	append(Args1, [XE], Args2),
	F =.. [Functor|Args2].

trans_body({C1, C2}, X0, XE, (C1, R)) :-
	trans_body({C2}, X0, XE, R), !.

trans_body({C}, X0, XE, (C, X0=XE)) :- !.
*/
