(*
Name: Matthew Le
ID: 3975089
Date: 2/6/2013
Problem 3 of Homework 1
*)

(*Part 1*)
signature BTREE = 
  sig
    type item
    val leq: item * item -> bool
    type tree
    val initTree: item -> tree
    val insert: item * tree -> tree
    val find: item -> tree -> bool
    val print: tree -> unit
  end;
  
(*Part 2*)  
signature ITEM = 
  sig
    type item 
    val leq: item * item -> bool
    val equalTo: item * item -> bool
    val toString: item -> string
  end;
    
(*Part 3*)
functor BTree(Item : ITEM) : BTREE = 
  struct
    type item = Item.item
    fun leq(p:item, q:item) : bool = Item.leq(p, q)
    fun equalTo(p:item, q:item) : bool = Item.equalTo(p, q)
    fun toString (p:item) : string = Item.toString(p)
    datatype tree = Empty
                   |Node of item * tree * tree
    
    fun initTree i = Node(i, Empty, Empty)
    fun insert (i, Empty) = Node(i, Empty, Empty)
       |insert (i, (Node(i', left, right))) = if leq(i, i')
                                           then Node(i',insert(i, left), right)
                                           else Node(i', left, insert(i, right))
    fun find i Empty = false
       |find i (Node(i', left, right)) = if equalTo(i, i')
                                         then true
                                         else if leq(i, i')
                                              then find i left
                                              else find i right
    fun print Empty = TextIO.print ""
       |print (Node(i, left, right)) = (print left;
                                        TextIO.print(toString(i) ^ ", ");
                                        print right)
  end;

(*Part 4*)
structure StringItem = 
  struct
    type item = string
    fun leq(i:item, j:item) = i <= j
    fun equalTo (i:item, j:item) = (i = j)    
    fun toString (i:item) = i
  end
    
structure IntItem = 
  struct
    type item = int
    fun leq(i:item, j:item) = i <= j
    fun equalTo (i:item, j:item) = (i = j)
    fun toString (i:item) = Int.toString(i)
  end
    

(*Part 5*)
structure iTree = BTree(IntItem)
val i1 = foldr iTree.insert (iTree.initTree(4)) [4, 2, 5, 123, 52, 1, 231, 2, 4, 34, 10, 6, 8, 5, 3, 2]  
  
   
   
structure sTree = BTree(StringItem)
val s1 = foldr sTree.insert (sTree.initTree("a")) ["c", "a", "b", "w", "k", "asd", "d", "p", "q", "h", "z"]

   
   
   
   
   
   
   
   
   
   
   
   
   
    
    
    
    
    


