s --> {nl}, a.

trans((H --> B), (TransH :- TransB)) :-
	trans_head(H, X0, X1, TransH),
	trans_body(B, X0, X1, TransB).

trans_head(H, X0, X1, F) :-
	atom(H),
	functor(F, H, 2),
	arg(1, F, X0),
	arg(2, F, X1).

trans_body((B1, B2), X0, XE, (F1, F2)) :-
	trans_body(B1, X0, XTemp, F1),
	trans_body(B2, XTemp, XE, F2).

trans_body(B, X0, XE, F) :-
	atom(B),
	functor(F, B, 2),
	arg(1, F, X0),
	arg(2, F, XE).

trans_body(B, X0, XE, true) :-
	is_list(B),
	prepend(B, XE, R),
	X0 = R.

trans_body({C1, C2}, X0, XE, (C1, R)) :-
	!, trans_body({C2}, X0, XE, R).

trans_body({C}, X0, XE, (C, X0=XE)) :- !.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

prepend([], L, L).
prepend([H|T], L, [H|R]) :-
	prepend(T, L, R).

	
