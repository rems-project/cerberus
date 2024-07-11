// TODO - revisit this Dhruv over-confident change

#ifndef CN_UTILS
void *cn_malloc(unsigned long long);
void cn_free_sized(void*, unsigned long long);
#endif

unsigned int deref(unsigned int *p)
/*@ trusted;
requires
    take v1_ = Owned(p);
ensures
    take v2 = Owned(p);
    v1_ == v2;
    return == v1_;
@*/
{
  return *p;
}

int main()
/*@ trusted; @*/
{
    unsigned int *p = cn_malloc(sizeof(unsigned int));
    *p = 5;
    unsigned int x = deref(p);
    /*@ assert (x == 5u32); @*/
    /*@ assert (*p == 5u32); @*/
    cn_free_sized(p, sizeof(unsigned int));
}
