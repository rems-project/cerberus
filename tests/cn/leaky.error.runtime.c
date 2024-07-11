// TODO - revisit this Dhruv over-confident change

#ifndef CN_UTILS
void *cn_malloc(unsigned long long);
void cn_free_sized(void*, unsigned long long);
#endif

unsigned int leaky_get (unsigned int *p)
/*@ trusted;
requires
    take v1_ = Owned(p);
ensures
    return == v1_;
@*/
{
  return *p;
}

int main()
/*@ trusted; @*/
{
    unsigned int *x = cn_malloc(sizeof(unsigned int));
    *x = 5;
    unsigned int res = leaky_get(x);
}
