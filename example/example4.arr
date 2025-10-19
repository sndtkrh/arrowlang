arrow main u : Unit ; u : Unit ~~> Unit {
    let res : Vec <~ return (
        let v : Vec = [1.0, 2.0] in
        let mat : Mat = mat[[2.0, 3.0],
                            [4.0, 5.0]] in
        (mat #> v)
    ) in
    let u : Unit <~ PrintVec res in
    let u : Unit <~ PrintVec (vec_zero 7) in
    PrintMat (mat_zero (3, 4))
}
