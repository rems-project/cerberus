int inc(int x)
/*@ requires x < 2147483647;
    ensures true; @*/
{
    return x + 1;
}
