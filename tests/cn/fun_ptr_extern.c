
int
f1 (int x, int y) {
  if (x > y) {
    return x - 1;
  }
  else {
    return y;
  }
}

extern int f2 (int x, int y);
/*@
spec f2 (integer x, integer y)
  requires true
  ensures true
@*/

typedef int int_binop1 (int, int);

typedef int_binop1 *int_binop;

int_binop g1 = f2;

/*@
predicate {integer x} Is_Known_Binop (pointer f) {
  assert (ptr_eq(f, &f1) || ptr_eq(f, &f2));
  return {x: 1};
}
@*/

int_binop
get_int_binop (int x)
/*@ ensures take X = Is_Known_Binop (return) @*/
{
  if (x == 0) {
    return f1;
  }
  else {
    return f2;
  }
}

int
call_site (int x, int y) {
  int_binop g2;
  int z;

  g2 = get_int_binop(y);
  z = g2 (x, y);

  return z;
}


