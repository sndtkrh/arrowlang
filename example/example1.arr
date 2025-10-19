arrow main u : Unit ; u : Unit ~~> Unit {
    handle
        let u : Unit <~ PrintInt 1 in
        return 300
    with {
        return x : Int => {
            let u : Unit <~ PrintInt x in
            return u
        }
        PrintInt k : Unit ~> Unit ; z : Int => {
            let u : Unit <~ PrintInt (z + 2000) in
            k @ u
        }
    }
}
