int main()
{
    int x = 0b110;
    int y = x & 0b101;
    /*@ assert(y == 4i32); @*/
    return 0;
}

