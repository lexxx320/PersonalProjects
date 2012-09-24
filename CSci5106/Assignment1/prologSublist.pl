sublist([], L).
sublist([X|L1], [X|L2]) :- sublist(L1, L2).




