effect {
    Op : Int * Int * Int ~> Int * Int
}

function f p , q : Int * Int --> Int * Int {
    (p + q + 20, p * q + 100)
}

arrow main _ : Unit ; _ : Unit ~~> Unit {
    handle
        let a, b : Int * Int <~ Op (3, 2, 2) in
        let _ : Unit <~ PrintInt a in
        PrintInt b
    with {
        return x : Unit => {
            return x
        }
        Op k : Int * Int ~> Unit ; s, t, u : Int * Int * Int => {
            k @ f (s, t + u)
        }
    }
}
