
arrow a u : Unit ; s : Int ~~> Int {
    let uu :Unit <~ PrintInt (s + 100) in
    return s
}

arrow main u2 : Unit ; u3 : Unit ~~> Unit {
    handle
        let x : Int <~ return 2 in
        let y : Int <~ (a u2) @ 9 in
        let u4 : Unit <~ PrintInt x in
        PrintInt (x + y)
    with {
        return u5 : Unit => {
            return u5
        }
        PrintInt k : Unit ~> Unit ; z : Int => {
            let u6 : Unit <~ PrintInt (z + 1000) in
            k @ u6
        }
    }
}
