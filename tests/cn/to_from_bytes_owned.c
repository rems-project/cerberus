int main()
{
    int x = 0;
    int *p = &x;
    /*@ to_bytes Owned(p); @*/
    unsigned char *p_char = (unsigned char *)p;
    /*@ extract Owned<unsigned char>, 2u64; @*/
    p_char[2] = 0xff;
    /*@ from_bytes Owned<int>(p); @*/
    /*@ assert (x == 16711680i32); @*/
    /*@ to_bytes Owned<int>(p); @*/
    /*@ from_bytes Owned<int>(p); @*/
    /*@ assert (x == 16711680i32); @*/
}
