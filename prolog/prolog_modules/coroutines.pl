:- module(coroutines, [freeze/2]).

freeze(X, Goal) :-
	nonvar(X),
	call(Goal).

freeze(X, Goal) :- 
	var(X),
	\+ get_attr(X, freeze, _),
	put_attr(X, freeze, Goal).

freeze(X, Goal) :-
	var(X),
	get_attr(X, freeze, Old_Goals),
	put_attr(X, freeze, (Old_Goals, Goal)).
