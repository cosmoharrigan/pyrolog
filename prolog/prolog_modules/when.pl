:- module(when, []).

attr_unify_hook(Goal, Value) :-
	\+ attvar(Value),
	call(Goal).

attr_unify_hook(Goal, Value) :-
	attvar(Value),
	coroutines:put_when_attributes([Value], Goal),
	walk_goals(Goal).

walk_goals(Goal) :-
	Goal \= (_, _),
	check_decidable(Goal).

walk_goals(Goals) :-
	Goals = (Goal, Rest),
	check_decidable(Goal),
	walk_goals(Rest).

check_decidable(Goal) :-
	Goal \= coroutines:when_decidable(_, _, _).

check_decidable(Goal) :-
	Goal = coroutines:when_decidable(_, _, _),
	Goal.
