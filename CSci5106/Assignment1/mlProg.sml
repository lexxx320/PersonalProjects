fun sublist [] [] = true
 |[] (a::listA) = true
 |(a::listA) [] = false
 |(a::listA) (b::listB) =
  if length(filter (== a) (a::listA)) == length(filter (== a) (b::listB))
  then sublist listA listB
  else false
