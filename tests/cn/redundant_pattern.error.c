/*@


 datatype seq {
    Nil {},
    Cons { integer head, datatype seq tail }
}

function [rec] (integer) sum(datatype seq xs) {
    match xs {
        Nil => { 0 }
        Cons { head : head , tail : tail } => { head + sum(tail) }
    }
}
@*/
