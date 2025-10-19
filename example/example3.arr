function relu x : Float --> Float {
    if (0.0 <. x) then x else 0.0
}

arrow main u : Unit ; u : Unit ~~> Unit {
    let f1 : Float <~ SampleNormal (0.0, 100.0) in
    let f2 : Float <~ SampleNormal (0.0, 1.0) in
    let f3 : Float <~ SampleNormal (0.0, 1.0) in
    let u : Unit <~ PrintFloat (relu f1) in
    let u : Unit <~ PrintFloat (relu f2) in
    let u : Unit <~ PrintFloat (relu f3) in
    return ()
}
