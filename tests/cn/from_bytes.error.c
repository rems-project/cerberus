int main()
{
    int x = 0;
    int *p = &x;
    /*@ to_bytes Owned(p); @*/
    /*@ from_bytes Alloc(p); @*/ // <-- proof fails here, but this is a no-op in runtime
    /*@ assert(false); @*/     // <-- so this is so that runtime testing also fails
}
