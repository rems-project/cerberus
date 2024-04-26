

/*@
type_synonym xy_tup = ({u32 x, u32 y})

function (xy_tup) mk_tup (u32 x, u32 y)
  { {x : x, y : y} }
@*/

void
f (unsigned int x, unsigned int y)
/*@ requires let tup = mk_tup(x, y); @*/ 
/*@ ensures tup == tup; @*/
{
  return;
}


