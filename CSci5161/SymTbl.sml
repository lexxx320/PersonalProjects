signature IntMapSig = 
sig
  type 'a map
  val apply : 'a map * int -> 'a
  val update : 'a map * int * 'a -> 'a map
  exception NotFound
end

functor IntMapFct() : IntMapSig = 
struct
  type 'a map = (int * 'a list) list
  datatype 'a map = Cons of int * 'a * 'a map
                   |Nil
  exception NotFound

  fun apply((Cons(i', l, rest)), i) = 
        if i = i'
        then l
        else apply(rest, i)
     |apply(Nil, i) = raise NotFound

  fun update((Cons(i', l, rest)), i, newList) = 
        if i = i'
        then Cons(i', newList, rest)
        else Cons(i', l, update(rest, i, newList))
     |update(Nil, i, newList) = Cons(i, newList, Nil)
end

signature ValSig = 
sig
  type value
end

functor ValFct() : ValSig = 
struct
  type value = real
end

signature SymSig = 
sig
  type sym
  val equal : sym * sym -> bool
  val hash : sym -> int
end

functor SymFct() : SymSig = 
struct
  type sym = string
  fun equal(s1, s2) = (s1 = s2)
  fun hash(s) = 
end

functor SymTblFct(
  structure IntMap : IntMapSig
  structure Val : ValSig
  structure Sym : SymSig) :

  sig 
  type table
  
  exception Lookup
  val lookup : table * Sym.sym -> Val.value
  val update : table * Sym.sym * Val.value -> table
  end =

  struct 
  datatype table = TBL of 
  (Sym.sym * Val.value) list IntMap.map

  exception Lookup
  
  fun find (sym,[]) = raise Lookup
    | find (sym, (sym',v)::rest) =
        if Sym.equal(sym,sym')  then v
        else find (sym,rest)

  fun lookup (TBL map, s) =
        let val n = Sym.hash(s)
            val l = IntMap.apply(map,n)
        in find (s,l)
        end handle IntMap.NotFound => raise Lookup

  fun update (TBL map, sym, v) = 
       let val n = Sym.hash(sym)
           val l = IntMap.apply(map, n) handle IntMap.NotFound => []
           val map' = IntMap.update(map, n, (sym, v) :: l)
           in TBL map'
           end

end


(*
Answer to Exercise 14:

In the previous example, "Sym" is used as a parameter to both 
SymTblFct and LexFct, so the sharing constraint is satisfied in 
ParseFct.  In the second example, they use two different calls
to SymFct(), which does not satisfy the sharing constraint
*)







