/* This will all fail with type error since they are bit vectors of different signs and sizes.
   Division should be done by bit vectors of the same sign and size.           */

int mod (int x, unsigned int y)
/*@ requires y != 0u32;
      let value = x % y;
    ensures return == value; @*/
{
    return x % y;
}

int mod_ (int x, long int y)
/*@ requires y != 0i64;
      let value = x % y;
    ensures return == value; @*/
{
    return x % y;
}

unsigned int mod__ (unsigned int x, int y)
/*@ requires y != 0i32;
      let value = x % y;
    ensures return == value; @*/
{
    return x % y;
}