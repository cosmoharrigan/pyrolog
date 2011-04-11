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

put_when_attributes([], _).
put_when_attributes([X|Rest], When_Goal) :-
	(get_attr(X, when, Current_Goals)
	->
		put_attr(X, when, (Current_Goals, When_Goal))
	;
		put_attr(X, when, When_Goal)
	),
	put_when_attributes(Rest, When_Goal).

when_impl(nonvar(X), Goal) :-
	(var(X)
	->
		put_when_attributes([X], Goal)
	;
		Goal
	).

when_impl(ground(X), Goal) :-
	term_variables(X, Varlist),
	(Varlist = []
	->
		Goal
	;
		[Var|_] = Varlist,
		put_when_attributes([Var], coroutines:when_impl(ground(Varlist), Goal))
	).

when_impl((A, B), Goal) :-
	when_impl(A, coroutines:when_impl(B, Goal)).

call_when_disjoint(Var, Goal) :-
	var(Var),
	Goal,
	Var = a.

call_when_disjoint(Var, _) :-
	nonvar(Var).

when_impl((A; B), Goal) :-
	when_impl(A, coroutines:call_when_disjoint(Z, Goal)),
	when_impl(B, coroutines:call_when_disjoint(Z, Goal)).

when_impl(?=(A, B), Goal) :-
	when_decidable(A, B, Goal).

when_impl(X, _) :-
	nonvar(X),
	functor(X, F, _),
	\+ (F == ','; F == ';'; F == 'ground'; F == 'nonvar'; F == '?='),
	throw(error(domain_error(when_condition, X))).

when_decidable(A, B, Goal) :-
	var(A),
	when_decidable_first_var(A, B, Goal).

when_decidable(A, B, Goal) :-
	nonvar(A),
	when_decidable_first_nonvar(A, B, Goal).

when_decidable_first_var(A, B, Goal) :-
	var(B),
	(A == B
	->
		Goal
	;
		put_when_attributes([A], coroutines:when_decidable(A, B, Goal))
	).

when_decidable_first_var(A, B, Goal) :-
	nonvar(B),
	put_when_attributes([A], coroutines:when_decidable(A, B, Goal)).

when_decidable_first_nonvar(A, B, Goal) :-
	var(B),
	put_when_attributes([B], coroutines:when_decidable(A, B, Goal)).

when_decidable_first_nonvar(A, B, Goal) :-
	nonvar(B),
	functor(A, FunctorA, ArityA),
	functor(B, FunctorB, ArityB),
	((FunctorA \= FunctorB; ArityA \= ArityB; (atomic(A), atomic(B)))
	-> 
		Goal
	;
		A =.. [Functor|ArgsA],
		B =.. [Functor|ArgsB],
		when_decidable_list(ArgsA, ArgsB, coroutines:call_when_disjoint(_, Goal))
	).

when_decidable_list([], [], _).
when_decidable_list([HeadA|RestA], [HeadB|RestB], Goal) :-
	when_decidable(HeadA, HeadB, Goal),
	when_decidable_list(RestA, RestB, Goal).

when(Cond, Goal) :-
	var(Cond), !,
	throw(error(instantiation_error)).

when(Cond, Goal) :-
	when_impl(Cond, user:Goal).

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
	%this_module(M),
	assert(user:Rule).

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
