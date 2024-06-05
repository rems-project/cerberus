

void f (int *p)
{
  unsigned long long p_int = (unsigned long long) p;
  int* q = __cerbvar_copy_alloc_id(p_int + 0ULL, p);
  /*@ assert (ptr_eq(p, q)); @*/
}

int main(void) {
  int p[1] = {1};
  f(p);
  return 0;
}