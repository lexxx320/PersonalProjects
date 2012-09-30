/*******************************************************
Name: Matthew Le
Student Id: 3975089
x500: lexxx320

Program Description: This program uses its first rule to 
pass in the first list as the third argument to the rest of
the rules.  The first rule for sublistHelper checks if the
first list is empty.  The second rule checks to see if the
head of both current lists are equal, if they are then check 
for the rest of each list.  For the last rule, if the heads of 
both lists are not equal, then the first list gets replaced with
its original list and it starts over again.
*******************************************************/


sublist(L, L2) :- sublistHelper(L, L2, L).

sublistHelper([], _, _).
sublistHelper([X|L1], [X|L2], L3) :- sublistHelper(L1, L2, L3).
sublistHelper([_|_], [_|L2], L3) :- sublistHelper(L3, L2, L3).




