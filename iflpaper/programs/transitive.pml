exception E
val i = IVar.new()
val j = IVar.new()
val _ = fork((|raise E, IVar.put(i, 10)|) 
            handle E => ((), ()))
val (_, x) = (|IVar.put(j, IVar.get i), IVar.get j|)
