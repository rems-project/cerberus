int main()
{
    int x = 0;
    int *p = &x;
    /*@ to_bytes Owned(p); @*/
    /*@ from_bytes Owned<int>(p); @*/
    /*@ to_bytes Owned<int>(p); @*/
    /*@ from_bytes Owned<int>(p); @*/
}
