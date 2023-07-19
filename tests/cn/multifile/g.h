extern int g (int x);

/*@ spec g (integer x)
  requires
    x >= 0
  ensures
    return == (mod (x, 12))
@*/

