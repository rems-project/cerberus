
/* this is a wrong specification. */
/* this function doesn't create an integer in memory */

int
f (int *p, int x)
/*@ requires x < 12 @*/
/*@ ensures return < 12 @*/
/*@ ensures take Resource_From_Nothing = Owned(p) @*/
{
  return x;
}



