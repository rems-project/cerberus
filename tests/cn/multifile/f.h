
extern int f (int x);

/*@ spec f (i32 x)
  requires
    x >= 0i32;
  ensures
    return == (mod (x, 12i32));
@*/

