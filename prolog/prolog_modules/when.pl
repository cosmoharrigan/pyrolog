:- module(when, []).

attr_unify_hook(Goal, Value) :-
	\+ attvar(Value),
	call(Goal).

attr_unify_hook(Goal, Value) :-
	attvar(Value),
	coroutines:put_when_attributes([Value], Goal).
