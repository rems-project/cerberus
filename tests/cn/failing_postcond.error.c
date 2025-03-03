int inc(int x)
/*@ requires x < 2147483647i32;
    ensures return < 2147483647i32; @*/
{
    return x + 1;
}
