import Prelude 

sublist (a:listA) (b:listB) = 
  if length (filter (== a) listA) <= length (filter (== a) listB)
  then sublist (tail listA) (tail listB)
  else False
sublist [] [] = True
sublist [] (b:listB) = True
sublist (a:listA) [] = False
  

