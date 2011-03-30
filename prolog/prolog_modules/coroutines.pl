:- module(coroutines, [freeze/2, when/2, frozen/2, block/1]).

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

% * FROZEN *

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
	nonvar(Cond),
	functor(Cond, ground, 1), !,
	term_variables(Cond, Varlist),
	(Varlist == []
	->
		this_module(M),
		call(M:(Goal))
	;
		[Var|_] = Varlist,
		put_when_attributes([Var], when(ground(Varlist), Goal))
	).

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

% *****************************************************
% *					   B L O C K                      *
% *****************************************************

block(Term) :-
	process_block_list(Term).

process_block_list(Term) :-
	Term \= (A, B),
	process_block(Term).
process_block_list((Head, Rest)) :-
	process_block(Head),
	process_block_list(Rest).

process_block(Block) :-
	Block =.. [Functor|Args],
	make_constraints(Args, Vars, Var_Constraints, When_Constraints),
	Header =.. [Functor|Vars],
	Rule = (Header :- (Var_Constraints, !, when(When_Constraints, Header))),
	this_module(M),
	assert(M:(Rule)).

make_constraints([], [], true, nonvar(_)).
make_constraints([Head|Rest], [X|Vars], (var(X), Var_Constraints), ';'(nonvar(X), When_Constraints)) :-
	nonvar(Head),
	Head = '-', !,
	make_constraints(Rest, Vars, Var_Constraints, When_Constraints).
make_constraints([X|Rest], [Var|Vars], Var_Constraints, When_Constraints) :-
	nonvar(X),
	\+ X = '-', !,
	make_constraints(Rest, Vars, Var_Constraints, When_Constraints).
make_constraints([X|_], _, _, _) :-
	var(X), !,
	throw(error(domain_error(nonvar, X))).
