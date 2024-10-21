int main()
{
    int x = 0;
    int *p = &x;
    /*@ to_bytes Owned(p); @*/
    char *p_char = (char *)p;
    /*@ extract Owned<char>, 2u64; @*/
    p_char[2] = 0xff;
    /*@ from_bytes Owned<int>(p); @*/
    /*@ assert (x == 16711680i32); @*/
    /*@ to_bytes Owned<int>(p); @*/
    /*@ from_bytes Owned<int>(p); @*/
    /*@ assert (x == 16711680i32); @*/
}
