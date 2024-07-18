#ifndef CN_UTILS
void *cn_malloc(unsigned long long);
void cn_free_sized(void*, unsigned long long);
#endif

int *malloc_int()
/*@ trusted;
    ensures take X = Block<int>(return); @*/
{
    return cn_malloc(sizeof(int));
}

void bad_free(int *p)
/*@ trusted; @*/
{
    cn_free_sized(p, sizeof(int));
}

int main()
/*@ trusted; @*/
{
    int *p = malloc_int();
    bad_free(p);
}
