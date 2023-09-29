

void f (int *p)
{
  /*@ assert (p == ((pointer) ((u64) p))); @*/
}
