function f s : Int --> Int {
    s + 1
}

arrow main u2 : Unit ; u3 : Unit ~~> Unit {
    handle
        let x : Int <~ return (f 2) in
        let y : Int <~ return (f 3) in
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
