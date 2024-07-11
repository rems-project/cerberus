// TODO - revisit this Dhruv over-confident change

#ifndef CN_UTILS
void *cn_malloc(unsigned long long);
void cn_free_sized(void*, unsigned long long);
#endif

unsigned int get (unsigned int *p)
/*@
requires
    take v1_ = Owned(p);
ensures
    take v2 = Owned(p);
    v2 == v1_; return == v1_;
@*/
{
  return *p;
}


unsigned int **bad(unsigned int *p)
/*@ trusted;
requires
    take v1_ = Owned(p);
ensures
    take v2 = Owned(p);
    take p2 = Owned(return);
    ptr_eq(p, p2);
    v1_ == v2;
@*/
{
    return &p;
}

int main()
/*@ trusted; @*/
{
    unsigned int *x = cn_malloc(sizeof(unsigned int));
    *x = 5;
    unsigned int res = get(x);
    /*@ assert (res == 5u32); @*/
    *x = 6;
    /*@ assert (*x == 6u32); @*/

    unsigned int **p = bad(x);
}
