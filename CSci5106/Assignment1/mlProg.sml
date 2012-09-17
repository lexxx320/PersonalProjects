fun filter f [] = []
  |filter f (x::xs) = 
    let val rst = filter f xs
  in
    if f x then x :: rst else rst
  end

fun sublist 
 |[] [] = true
 |[] (a::listA) = true
 |(a::listA) [] = false
 |(a::listA) (b::listB) =
  if length(filter (== a) (a::listA)) == length(filter (== a) (b::listB))
  then sublist listA listB
  else false
