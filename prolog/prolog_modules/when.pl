:- module(when, []).

attr_unify_hook(Goal, _) :-
	call(Goal).
