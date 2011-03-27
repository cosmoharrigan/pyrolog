:- module(freeze, []).

attr_unify_hook(Goals, _) :-
	call(Goals).
