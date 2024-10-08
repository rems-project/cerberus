void f (int *p)
/*@
requires
    has_alloc_id(p);
ensures
    true;
@*/
{
  unsigned long long p_int = (unsigned long long) p;
  int* q = __cerbvar_copy_alloc_id(p_int + 0ULL, p);
  /*@ assert (ptr_eq(p, q)); @*/
}

int main(void)
{
  int p[1] = {1};
  f(p);
}
