:- module(list, [append/3, member/2, is_list/1, select/3, nextto/3, memberchk/2, subtract/3]).

append([], L, L).
append([H|T], L, [H|R]) :- append(T, L, R).

member(E, [E|_]).
member(E, [_|T]) :- member(E, T).

is_list([]).
is_list([_|T]) :- is_list(T).

% borrowed from SWI prolog
select(X, [X|Tail], Tail).
select(Elem, [Head|Tail], [Head|Rest]) :-
	select(Elem, Tail, Rest).

% borrowed from SWI prolog
nextto(X, Y, [X,Y|_]).
nextto(X, Y, [_|Zs]) :-
	nextto(X, Y, Zs).

memberchk(Elem, List) :-
	once(member(Elem, List)).

% borrowed from SWI prolog
subtract([], _, []) :- !.                                                       
subtract([E|T], D, R) :-                                                        
	memberchk(E, D), !,                                                     
	subtract(T, D, R).                                                      
subtract([H|T], D, [H|R]) :-                                                    
	subtract(T, D, R).
