/* A local which is never written to, and never read.

   The usual elaboration writes to every C local var at least once, so this
   case cannot arise there - but the CN backend does not, which is why
   find_promotable starts from the not-escaped vars and removes the
   non-promotable ones, rather than starting from the ones with a write
   footprint. */
int main()
{
    int x;
    return 0;
}
