/* Integer promotions in divisions are subtle. The result of a division will be the larger type,
according to the following hierarchy `iN <: uN` and `uN <: i(2N)`  (and of course `iN <: i(2N)` and `uN <: u2N`).

Important: (1) signed integers must be non-negative to convert to unsigned (2) if one of the operands
is unsigned, the result will be unsigned, so any signed values must be non-negative. */
 
unsigned int division (unsigned int x, int y)    
/*@ requires y > 0i32;
    ensures return == x/(u32)y; @*/
{                                               
    return x/y;
}