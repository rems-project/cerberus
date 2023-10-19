

void f (int *p)
{
  unsigned long long p_int = (unsigned long long) p;
  int* q = __cerbvar_copy_alloc_id(p_int + 0ULL, p);
  /*@ assert (p == q); @*/
}
