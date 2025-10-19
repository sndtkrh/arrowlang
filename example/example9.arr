effect {
    Op : Int ~> Int
}

arrow b u : Unit ; x : Int ~~> Int {
    Op x
}

arrow a n : Int ; x : Int ~~> Int {
    handle
        b () @ x
    with {
        return r : Int => {
            return r
        }
        Op k : Int ~> Int ; z : Int => {
            k @ (n + z)
        }
    }
}

arrow main u : Unit ; u : Unit ~~> Unit {
    let l : Int <~ a 2 @ 3 in
    PrintInt l
}
