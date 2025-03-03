int main()
{
    int x = 0;
    int *p = &x;
    /*@ to_bytes RW(p); @*/
    unsigned char *p_char = (unsigned char *)p;
    /*@ focus RW<unsigned char>, 2u64; @*/
    p_char[2] = 0xff;
    /*@ from_bytes RW<int>(p); @*/
    /*@ assert (x == 16711680i32); @*/
    /*@ to_bytes RW<int>(p); @*/
    /*@ from_bytes RW<int>(p); @*/
    /*@ assert (x == 16711680i32); @*/
}
