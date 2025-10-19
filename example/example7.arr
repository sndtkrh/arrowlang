effect {
    Get : Unit ~> Int
}
arrow main u2 : Unit ; u3 : Unit ~~> Unit {
    handle
        let x : Int <~ return 2 in
        let y : Int <~
                ar s : Int ~~> {
                    let t : Int <~ Get () in
                    return s
                } @ 9
        in
        return x
    with {
        return x1 : Int => {
            return ()
        }
        Get k : (Int ~> Unit) ; u : Unit => {
            k @ 100
        }
    }
}
