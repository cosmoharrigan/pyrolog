:- module(freeze, []).

attr_unify_hook(Goals, X) :-
	nonvar(X),
	Goals.

attr_unify_hook(Goals, X) :-
	attvar(X),
	get_attr(X, freeze, Current_Goal),
	put_attr(X, freeze, (Goals, Current_Goal)).
	
attr_unify_hook(Goals, X) :-
	attvar(X),
	\+ get_attr(X, freeze, Current_Goal).

attr_unify_hook(Goals, X) :-
	\+ attvar(X),
	var(X).
