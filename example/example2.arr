function f x : Int --> Int {
    x + 10
}

function g x : Int --> Int {
    x + 200
}

function h x : Int --> Int {
    x + 8000
}

arrow main u : Unit ; u : Unit ~~> Unit {
    handle
        let n : Int <~ return 3 in
        let m : Int <~ return (h 5) in
        let u : Unit <~ PrintInt (f m) in 
        PrintInt (f n)
    with {
        return u : Unit => {
            return u
        }
        PrintInt k : Unit ~> Unit ; z : Int => {
            let u : Unit <~ PrintInt (g z) in
            (k @ u)
        }
    }
}
