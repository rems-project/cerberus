int foo(int x)
/*@ requires x < MAXi32();
    ensures return == x + 1i32; @*/
/*@ requires x < MAXi32(); @*/
{
    return x + 1;
}
