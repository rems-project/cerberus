
extern int f (int x);

/*@ spec f (integer x)
  requires
    x >= 0
  ensures
    return == (mod (x, 12))
@*/

