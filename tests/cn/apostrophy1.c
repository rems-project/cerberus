//NOTE:
/* You can use an apostrophe to separate numeric value and its sign and size.

   For example: You can now do 3'i32 for 3i32. 

   It makes it much more readable. */

int add_or_subtract (int x, int y)
/*@ requires let sum = (i64) x + (i64) y;
             let diff = (i64) x - (i64) y;
            -2147483648'i64 <= sum; sum <= 2147483647'i64;
            -2147483648'i64 <= diff; diff <= 2147483647'i64;
            let five = 5'u64;
    ensures return == ((x > y) ? (i32) diff : (i32) sum); 
@*/
{
    if (x > y)
    {
        return x - y;
    }

    return x + y;

}

// NOTE: 
/* You can still do the regular 3i32 like nothing ever happened. */

int add_or_subtract_ (int x, int y)
/*@ requires let sum = (i64) x + (i64) y;
             let diff = (i64) x - (i64) y;
            -2147483648i64 <= sum; sum <= 2147483647i64;
            -2147483648i64 <= diff; diff <= 2147483647i64;
            let five = 5u64;
    ensures return == ((x > y) ? (i32) diff : (i32) sum);
@*/
{
    if (x > y)
    {
        return x - y;
    }

    return x + y;

}
