:- module(coroutines, [freeze/2, when/2]).

% *****************************************************
% *                  F R E E Z E                      *
% *****************************************************

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

% *****************************************************
% *                    W H E N                        *
% *****************************************************

wellformed(Cond, Goal) :-
	\+ var(Cond),
	\+ var(Goal), !,
	wellformed(Cond).
wellformed(Cond, Goal) :-
	(var(Cond); var(Goal)),
	throw(error(instanciation_error)).
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
	throw(error(instanciation_error)).
wellformed(ErrorCond) :-
	throw(error(domain_error(when_condition, ErrorCond))), !.

put_when_attributes([], _).
put_when_attributes([X|Rest], When_Goal) :-
	put_attr(X, when, When_Goal),
	put_when_attributes(Rest, When_Goal).

when(Cond, Goal) :-
	wellformed(Cond, Goal),
	ground(Cond), !,
	this_module(M),
	call(M:(Goal)).

when(Cond, Goal) :-
	wellformed(Cond, Goal),
	term_variables(Cond, Vars),
	this_module(M),
	put_when_attributes(Vars, (Cond -> M:(Goal); true)).
