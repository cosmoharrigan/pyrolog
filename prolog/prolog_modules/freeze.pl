:- module(freeze, []).

attr_unify_hook(Goals, _) :-
	this_module(M),
	call(M:Goals).
