int main()
{
    int x = 0;
    int *p = &x;
    /*@ to_bytes Owned(p); @*/
    /*@ from_bytes each (u64 i; 0u64 <= i && i < 8u64) { Alloc(array_shift<char>(p,i)) }; @*/ // <-- proof fails here, but this is a no-op in runtime
    /*@ assert(false); @*/     // <-- so this is so that runtime testing also fails
}
