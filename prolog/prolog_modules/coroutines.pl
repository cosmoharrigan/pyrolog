:- module(coroutines, [freeze/2, when/2, frozen/2]).

% *****************************************************
% *                  F R E E Z E                      *
% *****************************************************

freeze(X, Goal) :-
	nonvar(X),
	this_module(M),
	call(M:(Goal)).

freeze(X, Goal) :- 
	var(X),
	this_module(M),
	\+ get_attr(X, freeze, _),
	put_attr(X, freeze, M:(Goal)).

freeze(X, Goal) :-
	var(X),
	this_module(M),
	get_attr(X, freeze, Old_Goals),
	put_attr(X, freeze, (Old_Goals, M:(Goal))).

% * FROZEN

frozen(X, true) :-
	nonvar(X).

frozen(X, true) :-
	var(X),
	\+ get_attr(X, freeze, _).

frozen(X, R) :-
	var(X),
	get_attr(X, freeze, R).

% *****************************************************
% *                    W H E N                        *
% *****************************************************

wellformed(Cond, Goal) :-
	(\+ var(Cond)
	->
		wellformed(Cond)
	;
		throw(error(instantiation_error))
	).
wellformed(ground(_)) :- !.
wellformed(nonvar(_)) :- !.
wellformed(?=(_, _)) :- !.
wellformed(','(Cond1, Cond2)) :-
	wellformed(Cond1),
	wellformed(Cond2), !.
wellformed(';'(Cond1, Cond2)) :-
	wellformed(Cond1),
	wellformed(Cond2), !.
wellformed(ErrorCond) :-
	var(ErrorCond), !,
	throw(error(instantiation_error)).
wellformed(ErrorCond) :-
	throw(error(domain_error(when_condition, ErrorCond))), !.

put_when_attributes([], _).
put_when_attributes([X|Rest], When_Goal) :-
	(get_attr(X, when, Current_Goals)
	->
		put_attr(X, when, (Current_Goals, When_Goal))
	;
		put_attr(X, when, When_Goal)
	),
	put_when_attributes(Rest, When_Goal).

when(Cond, Goal) :-
	wellformed(Cond, Goal),
	call(Cond), !,
	this_module(M), 
	call(M:(Goal)).

when(Cond, Goal) :-
	wellformed(Cond, Goal),
	term_variables(Cond, Vars),
	this_module(M),
	put_when_attributes(Vars, (Cond -> M:(Goal); true)).
