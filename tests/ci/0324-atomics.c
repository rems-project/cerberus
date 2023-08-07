struct T1 {
  int x;
};

struct T2 {
  int x, y;
};

_Atomic(int) glob = 10;
_Atomic(struct T2) glob_st;

int func(int x, _Atomic(int) y)
{
  return y;
}

int xxx = 100;
_Atomic(int) *ptr_to_atomic = &glob;
_Atomic(int*) atomic_ptr = &xxx;

_Atomic(int*) p, q;
int *r;

int* func2(_Atomic(int*) arg1, int *arg2)
{
  return arg1;
}

_Atomic(int*) func3(int *arg2)
{
  return arg2;
}

int main(void)
{
  int x = 100;
  _Atomic(int) local = 20;
  glob = 30;
  local = 40;
  glob;
  local;

  _Atomic(struct T2) st1, st2;
  struct T2 st3 = {1,2};
  st1 = st2;
  st1 = st3;
  st3 = st2;

  func(glob, x);
  func(local, x);
  func(x, glob);
  func(x, local);
  
  q = &xxx;
  p = q;
  r = p;
  q = r;
  func2(r, p);
  func2(p, r);
  func3(r);
  
  glob + 1;
  if (glob)
    return *atomic_ptr + glob + *ptr_to_atomic;
}