import Prelude

a = [1..5]
b = [1..10]
c = [1, 2, 3, 9]
d = [1, 2, 3, 11]

--This function looks at four different cases
--Case1: both list are empty return true
--Case2: First list is empty return true
--Case3: Second list is empty return false
--Case4: Neither are empty, then if the instances of head of a is equal to the instances of head of a in B, then return sublist of the two list's tails, otherwise return false
sublist [] [] = True
sublist [] (b:listB) = True
sublist (a:listA) [] = False
sublist (a:listA) (b:listB) = 
  if length(filter (== a) (a:listA)) <= length(filter (== a) (b:listB))
  then sublist listA listB
  else False


