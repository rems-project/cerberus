/*@

datatype point {
    Point { integer x , integer y }
}

datatype seq {
    Nil {},
    Cons { point head, datatype seq tail }
}

function [rec] (integer) sum(datatype seq xs) {
    match xs {
        Nil {} => { 0 }
        Cons { head : Point { x : a , y : a } , tail : tail } => { a + b + sum(tail) }
    }
}
@*/
