val i = IVar.new()
exception E
val _ = fork((|raise E, IVar.put(i, 10)|)
            handle E => ((), ()))
val x = IVar.get i
val _ = fork (IVar.get i)
