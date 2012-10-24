(*--Matthew Le
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

--Lists for testing purposes*)
val a = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
val b = [1, 2, 3, 4, 5]
val c = [1, 2, 1, 2]
val d = [1, 2, 3, 5, 4]
val e = [1, 2, 4, 5]

fun sublistHelper [] listA [] = true
  |sublistHelper [] listA (b::listB) = true
  |sublistHelper (a::listA) listA2 [] = false
  |sublistHelper (a::listA) origListA (b::listB) = 
    if a = b
    then sublistHelper listA origListA listB
    else sublistHelper origListA origListA listB

fun sublist listA listB = sublistHelper listA listA listB


