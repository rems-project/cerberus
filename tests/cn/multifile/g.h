extern int g (int x);

/*@ spec g (i32 x)
  requires
    x >= 0i32
  ensures
    return == (mod (x, 12i32))
@*/

