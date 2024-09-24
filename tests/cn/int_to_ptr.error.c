int* cast(unsigned long long addr)
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
    int* p = cast((unsigned long long)&x);
    // The cast is successful, but has an unconstrained allocation ID, and so
    // can't be used
    return *p == 0;
}
