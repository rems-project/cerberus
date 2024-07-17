#ifndef CN_UTILS
void *cn_malloc(unsigned long long);
void cn_free_sized(void*, unsigned long long);
#endif

unsigned int *mkref(unsigned int x)
/*@ trusted;
requires
    true;
ensures
    take v1_ = Owned(return);
    v1_ == x;
@*/
{
  unsigned int *p = cn_malloc(sizeof(unsigned int));
  *p = x;
  return p;
}

int main()
/*@ trusted; @*/
{
    unsigned int *p = mkref(5);
    /*@ assert (*p == 5u32); @*/
    // TODO - consider decrementing stack-depth for main too?
    // or it doesn't matter? main can be called multiple times.
}
