:- module(list, [append/3, member/2, is_list/1]).

append([], L, L).
append([H|T], L, [H|R]) :- append(T, L, R).

member(E, [E|_]).
member(E, [_|T]) :- member(E, T).

is_list([]).
is_list([_|T]) :- is_list(T).
