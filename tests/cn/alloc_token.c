#ifndef CN_UTILS
void *cn_malloc(unsigned long long);
void cn_free_sized(void*, unsigned long long);
#endif

void free_int(int *p)
/*@
trusted;
requires
    take log = Alloc(p);
    allocs[(alloc_id)p] == log;
    let base = array_shift<char>(p, -2i64);
    log.base == (u64) base;
    log.size == sizeof<int>;
    take i = Block<int>(base);
ensures
    true;
@*/
{
    cn_free_sized(p, sizeof(int));
}

int *malloc_int()
/*@
trusted;
ensures
    take log = Alloc(return);
    allocs[(alloc_id)return] == log;
    log.base == (u64) return;
    log.size == sizeof<int>;
    take i = Block<int>(return);
@*/
{
    return cn_malloc(sizeof(int));
}

int main()
/*@ trusted; @*/
{
    int *p = malloc_int();
    *p = 4;
    free_int(p);
}
