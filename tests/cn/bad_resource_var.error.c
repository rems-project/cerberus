void inc(int* p)
/*@ requires take X = Owned(p);
             X < 2147483647i32; @*/
/*@ ensures take X2 = Owned(p);
            X2 < 2147483647i32; @*/
{
    *p += 1;
}
