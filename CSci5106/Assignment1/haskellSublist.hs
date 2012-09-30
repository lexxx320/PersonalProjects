import Prelude

a = [1..5]
b = [1..10]
c = [1, 2, 3, 9]
d = [1, 2, 9, 3]
e = [1,2,3,5,4]
--Matthew Le
--3975089
--lexxx320

--This function looks at four different cases
--Case1: both list are empty return true
--Case2: First list is empty return true
--Case3: Second list is empty return false
--Case4: Neither are empty then,
--If the first element in listA is equal to the first
--element in list b, then check for the rest of the list
--If not, then restart listA and check against the rest of listB

sublist listA listB = sublistHelper listA listA listB

sublistHelper (a:listA) origListA (b:listB) = 
  if a == b 
  then sublistHelper listA origListA listB
  else sublistHelper origListA origListA listB
sublistHelper [] listA [] = True
sublistHelper [] listA (b:listB) = True
sublistHelper (a1:listA1) listA [] = False
