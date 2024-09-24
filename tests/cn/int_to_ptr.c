void* cast(unsigned long long addr)
/*@
ensures
    addr == 0u64 && is_null(return) || addr != 0u64 && has_alloc_id(return) && (u64) return == addr;
@*/
{
    return (void*)addr;
}

int main()
{
    int x = 0;
    void* p = cast((unsigned long long)&x);
    /*@ assert ((u64) &x == 0u64 || has_alloc_id(p) && (u64) p == (u64) &x); @*/
}
