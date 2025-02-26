
/* this is a wrong specification. */
/* this function doesn't create an integer in memory */

int
f (int *p, int x)
/*@ requires x < 12i32;
    ensures return < 12i32;
            take Resource_From_Nothing = Owned(p); @*/
{
  return x;
}



