:- module(coroutines, [freeze/2, when/2, frozen/2, block/1]).
:- meta_predicate freeze('?', :), when('?', :), block(:).

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
	coroutines:put_when_attributes(Rest, When_Goal).

when_impl(nonvar(X), Goal) :-
	(var(X)
	->
		coroutines:put_when_attributes([X], Goal)
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
		coroutines:put_when_attributes([Var], coroutines:when_impl(ground(Varlist), Goal))
	).

when_impl((A, B), Goal) :-
	coroutines:when_impl(A, coroutines:when_impl(B, Goal)).

call_when_disjoint(Var, Goal) :-
	var(Var),
	Var = a,
	Goal.

call_when_disjoint(Var, _) :-
	nonvar(Var).

when_impl((A; B), Goal) :-
	coroutines:when_impl(A, coroutines:call_when_disjoint(Z, Goal)),
	coroutines:when_impl(B, coroutines:call_when_disjoint(Z, Goal)).

when_impl(?=(A, B), Goal) :-
	coroutines:when_decidable(A, B, Goal).

when_impl(X, _) :-
	nonvar(X),
	functor(X, F, _),
	\+ (F == ','; F == ';'; F == 'ground'; F == 'nonvar'; F == '?='),
	throw(error(domain_error(when_condition, X))).

when_decidable(A, B, Goal) :-
	var(A),
	coroutines:when_decidable_first_var(A, B, Goal).

when_decidable(A, B, Goal) :-
	nonvar(A),
	coroutines:when_decidable_first_nonvar(A, B, Goal).

when_decidable_first_var(A, B, Goal) :-
	var(B),
	(A == B
	->
		Goal
	;
		coroutines:put_when_attributes([A], coroutines:when_decidable(A, B, Goal))
	).

when_decidable_first_var(A, B, Goal) :-
	nonvar(B),
	coroutines:put_when_attributes([A], coroutines:when_decidable(A, B, Goal)).

when_decidable_first_nonvar(A, B, Goal) :-
	var(B),
	coroutines:put_when_attributes([B], coroutines:when_decidable(A, B, Goal)).

when_decidable_first_nonvar(A, B, Goal) :-
	nonvar(B),
	(?=(A, B)
	-> 
		Goal
	;
		New_Goal = coroutines:call_when_disjoint(_X, Goal),
		term_variables(A, VarsA),
		term_variables(B, VarsB),
		put_when_attributes(VarsA, coroutines:when_decidable(A, B, New_Goal)),
		put_when_attributes(VarsB, coroutines:when_decidable(A, B, New_Goal))
	).
	
when(Cond, Goal) :-
	var(Cond), !,
	throw(error(instantiation_error)).

when(Cond, Goal) :-
	coroutines:when_impl(Cond, Goal).

% *****************************************************
% *					   B L O C K                      *
% *****************************************************

block(Module:Term) :-
	coroutines:process_block_list(Term, Module).

process_block_list(Term, Module) :-
	Term \= (A, B),
	coroutines:process_block(Term, Module).
process_block_list((Head, Rest), Module) :-
	coroutines:process_block(Head, Module),
	coroutines:process_block_list(Rest, Module).

process_block(Block, Module) :-
	Block =.. [Functor|Args],
	coroutines:make_constraints(Args, Vars, Var_Constraints, When_Constraints),
	Header =.. [Functor|Vars],
	Rule = (Header :- (Var_Constraints, !, when(When_Constraints, Header))),
	assert(Module:Rule).

make_constraints([], [], true, nonvar(_)).
make_constraints([Head|Rest], [X|Vars], (var(X), Var_Constraints), ';'(nonvar(X), When_Constraints)) :-
	nonvar(Head),
	Head = '-', !,
	coroutines:make_constraints(Rest, Vars, Var_Constraints, When_Constraints).
make_constraints([X|Rest], [Var|Vars], Var_Constraints, When_Constraints) :-
	nonvar(X),
	\+ X = '-', !,
	coroutines:make_constraints(Rest, Vars, Var_Constraints, When_Constraints).
make_constraints([X|_], _, _, _) :-
	var(X), !,
	throw(error(domain_error(nonvar, X))).
