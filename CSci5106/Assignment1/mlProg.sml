fun filter f [] = []
  |filter f (x::xs) = 
    let val rst = filter f xs
  in
    if f x then x :: rst else rst
  end

fun equal a b = (a = b)

val a = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
val b = [1, 2, 3, 4, 5]
val c = [1, 2, 1, 2]
val d = [1, 11, 21, 31]
val e = [1, 21, 31, 11]

fun sublist [] [] = true
 |sublist [] (a::listA) = true
 |sublist (a::listA) [] = false
 |sublist (a::listA) (b::listB) =
  let 
    val currentSizeA = length(filter (equal a) (a::listA))
    val currentSizeB = length(filter (equal a) (b::listB))
  in
    if currentSizeA = currentSizeB
    then sublist listA listB
    else false
  end

