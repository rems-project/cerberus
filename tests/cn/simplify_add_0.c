signed int left_zero(signed int x, signed int y)                                     
/*@ requires x == 0i32; @*/                                                          
/*@ ensures return == y; @*/                                                         
{                                                                                
  return x + y;                                                                  
}

signed int right_zero(signed int x, signed int y)                                     
/*@ requires y == 0i32; @*/                                                          
/*@ ensures return == x; @*/                                                         
{                                                                                
  return x + y;                                                                  
}

int main(void)
{
  int r1 = left_zero(0, 42);
  int r2 = right_zero(5, 0);
}
