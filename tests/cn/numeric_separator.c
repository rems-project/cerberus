void numeric_separator() 
/*@ requires 
  10i32 == 10_i32;      // Decimal 
  0x10i32 == 0x1_0i32;  // Hex
  010i32 == 01_0i32;    // Octal 
  0b10i32 == 0B1_0i32;  // Binary 
@*/
{
  ; 
}