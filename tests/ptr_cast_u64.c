

typedef unsigned long long u64;


int
foo (int *p, u64 *childp)
{
  u64 x;
  x = (u64)childp;
  x = (u64)p;
  return 1;
}
