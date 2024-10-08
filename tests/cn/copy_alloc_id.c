void f1 (int *p)
/*@
requires
    take B = Block(p);
ensures
    take B2 = Block(p);
@*/
{
  unsigned long long p_int = (unsigned long long) p;
  int* q = __cerbvar_copy_alloc_id(p_int + 0ULL, p);
  /*@ assert (ptr_eq(p, q)); @*/
}

void f2 (int *p)
/*@
requires
    take A = Alloc(p);
    A.base <= (u64) p;
    (u64) p <= (u64) p + sizeof<int>;
    (u64)p + sizeof<int> <= A.base + A.size;
    has_alloc_id(p);
ensures
    take A2 = Alloc(p);
    A == A2;
@*/
{
  unsigned long long p_int = (unsigned long long) p;
  int* q = __cerbvar_copy_alloc_id(p_int + 0ULL, p);
  /*@ assert (ptr_eq(p, q)); @*/
}

int main(void)
{
  int p[1] = {1};
  /*@ extract Owned<int>, 0u64; @*/
  f1(p);
  f2(p);
}
