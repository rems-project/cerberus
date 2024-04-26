
/*@
datatype mylist {
  Nil {},
  Cons {integer hd, datatype mylist tl}
}

function (integer) snd (datatype mylist t) {
  match t {
    Cons {hd: _, tl: Cons {hd: v, tl: _}} => { v }
    Nil {} => { 0 }
  }
}
@*/

void
check_foo (int x)
/*@ ensures snd(Cons {hd: 10, tl: Cons {hd: 20, tl: Nil {}}}) == 20; @*/
{
}


