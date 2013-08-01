:- module(list, [append/3, member/2, is_list/1, select/3, nextto/3, memberchk/2, subtract/3, min_member/2, max_member/2, delete/3, length/2]).

append([], L, L).
append([H|T], L, [H|R]) :- append(T, L, R).

member(E, [E|_]).
member(E, [_|T]) :- member(E, T).

is_list([]).
is_list([_|T]) :- is_list(T).

% length/2
length(List, Len) :-
	(nonvar(Len) -> Len > -1; true),
	is_list(List),
	length(List, 0, Len).

length([], Len, Len).
length([Head | Tail], LenIn, LenOut) :-
	LenDown is LenIn + 1,
	length(Tail, LenDown, LenOut).

% min_member/2
min_member(Result, [H | T]) :-
	min_member(H, T, Result).

min_member(Result, [], Result).
min_member(BestIn, [H | T], BestOut) :-
	(BestIn @< H -> BestDown = BestIn; BestDown = H),
	min_member(BestDown, T, BestOut).

% max_member/2
max_member(Result, [H | T]) :-
	max_member(H, T, Result).

max_member(Result, [], Result).
max_member(BestIn, [H | T], BestOut) :-
	(BestIn @> H -> BestDown = BestIn; BestDown = H),
	max_member(BestDown, T, BestOut).

% subtract/3
subtract(Rest, [], Rest).
subtract(_, Delete, _) :-
	var(Delete), !, fail.
subtract(Set, [Elem | Delete], Result) :-
	delete(Set, Elem, Rest),
	subtract(Rest, Delete, Result), !.

% delete/3
delete([], _, []).
delete([Elem | List1], Elem, List2) :-
	delete(List1, Elem, List3), !,
	List2 = List3.
delete([Head | List1], Elem, List2) :-
	delete(List1, Elem, List3),
	List2 = [Head | List3].

% memberchk/3
memberchk(Elem, [Elem | _]) :- !.
memberchk(Elem, [_ | List]) :-
	memberchk(Elem, List).

% nextto/3
nextto(X, Y, [A, B | _]) :-
	X = A, Y = B, true.
nextto(X, Y, [_, B | List]) :-
	nextto(X, Y, [B | List]).

% select/3
select(Elem, [Elem | List1], List1).
select(Elem, [Head | List1], [Head | List3]) :-
	select(Elem, List1, List3).
