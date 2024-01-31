
int
f1 (int x, int y) {
  if (x > y) {
    return x - 1;
  }
  else {
    return y;
  }
}

int
f2 (int x, int y) {
  int z;

  z = f1 (x, y);

  return z;
}

int
f3 (int x, int y) {
  if (y >= 0 && x > y) {
    return x - y;
  }
  else {
    return x;
  }
}


typedef int int_binop1 (int, int);

typedef int_binop1 *int_binop;

int_binop g1 = f2;

/*@
predicate (void) Is_Binop (pointer f) {
  assert (in_loc_list (f, [&f1, &f2, &f3]));
  return;
}
@*/

int_binop
get_int_binop (int x)
/*@ ensures take X = Is_Binop (return) @*/
{
  if (x == 0) {
    return f1;
  }
  else if (x == 1) {
    return f2;
  }
  else {
    return f3;
  }
}

int
call_site (int x, int y) {
  int_binop g2;
  int z;

  g2 = get_int_binop(y);
  /*@ split_case (ptr_eq (g2, &f1)); @*/;
  /*@ split_case (ptr_eq (g2, &f2)); @*/;
  z = g2 (x, y);

  return z;
}


