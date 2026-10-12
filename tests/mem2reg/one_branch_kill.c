/* Derived from tests/ci/0112-call_in_label.c (minus the call, which the
   analysis does not track anyway).

   One arm of the if kills x - via the return - before running the label,
   and the other does not. The use-after-free check has to accept that
   mismatch, because control does not return from the run to the join
   point. */
int main(void)
{
  int x = 0;
 l:
  if (x)
    return 0;
  x = 1;
  goto l;
}
