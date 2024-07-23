int main()
{
    int x = 0;
    int y = ~x;
    /*@ assert(y == -1i32); @*/
    return 0;
}
