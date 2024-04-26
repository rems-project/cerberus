int foo(int x)
/*@ requires
              x < 2147483647 + function; @*/
{
    return x + 1;
}

