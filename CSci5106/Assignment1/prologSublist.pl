sublist([], _).
sublist([X|L1], [X|L2]) :- sublist(L1, L2).
sublist([X|L1], [_|L2]) :- sublist([X|L1], L2).

sublist(L, [1, 2,3, 4, 5]).



