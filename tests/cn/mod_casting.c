/* NOTE: Recommend not casting bits to make modulo possible between ints of different sizes.
  
   In C, when modulo occurs between two different int types, the quotient will the larger type.
   With this in mind, the highest parameter int value should be the return value of the function.
   To reflect this in your CN specification, you must cast the lower bit value to the higher bit value
   in the division operation. 

   Casting hierarchy: int = i32 --> unsigned int = u32 --> long int = i64 --> long unsigned int = u64

   IMPORTANT: 
   1. You shouldn't try to convert a higher bit type to lower one in a modulo operation. It won't work out.
   2. sign to unsigned conversions, the signed bit must be greater than 0. Negative values conversion aren't pretty.
   3. signed divided by unsigned and their converse results in unsigned. So make sure signed values positive.
*/

// SUCCESSES and successful converses

unsigned int mod (unsigned int x, int y)    // unsigned int mod (int x, unsigned int y)
/*@ requires y > 0i32;                      // $ requires y != 0u32 && x >= 0i32;
     ensures return == x % (u32)y; @*/      //   ensures return == (u32)x % y;   $
{                                           // {
    return x % y;                           //      return x % y;
}                                           // }

long int mod_ (long int x, int y)           // long int mod_ (int x, long int y)
/*@ requires y != 0i32;                     // $ requires y != 0i64;
    ensures return == x %(i64) y; @*/       //   ensures return == (i64)x % y; $
{                                           // {
    return x % y;                           //      return x % y;
}                                           // }

long int mod__ (long int x, unsigned int y)      // long int mod__ (unsigned int x, long int y)
/*@ requires x >= 0i64 && y != 0u32;             // $ requires y > 0i64;
    ensures return == x % (i64)y; @*/            //   ensures return == (i64)x % y; $
{                                                // {
    return x % y;                                //      return x % y;
}                                                // }

long unsigned int mod___ (long unsigned int x, long int y)       // long unsigned int mod__ (long int x, long unsigned int y)
/*@ requires y > 0i64;                                           // $ requires x >= 0i64 && y != 0u64;
    ensures return == x % (u64)y; @*/                            //   ensures return == (u64)x % y; $
{                                                                // {
    return x % y;                                                //      return x % y;
}                                                                // }