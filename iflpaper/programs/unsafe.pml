exception E
val i = IVar.new()
val _ = (|raise E, IVar.put(i, 10)|)
        handle E => ((), ())
val x = IVar.get i
