void preserve(int size, int *p)
/*@
requires
  take a1 = each(u64 i; 0u64 <= i && i < (u64)size) { Owned<int>(array_shift<int>(p,i)) };
ensures
  take a2 = each(u64 i; 0u64 <= i && i < (u64)size) { Owned<int>(array_shift<int>(p,i)) };
@*/
{
}
