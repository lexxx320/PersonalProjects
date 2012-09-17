fun sublist [] [] = true
 |[] (a::listA) = true
 |(a::listA) [] = false
 |(a::listA) (b::listB) =
  if length(filter (== a) listA) == length(filter (== a) listB)
  then sublist (tail a) (tail b)
  else false
