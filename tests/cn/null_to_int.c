unsigned long long f(int *p)
/*@
requires
    ptr_eq(p, NULL);
ensures
    return == 0u64;
@*/
{
    return (unsigned long long)p;
}

int main()
{
    return f((int*)0);
}
