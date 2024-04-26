
int
test_cast_loc_to_various (int *p)
/*@ requires let x1 = ((u64) p); @*/
/*@ requires let x2 = ((u32) p); @*/
/*@ requires let x3 = ((i64) p); @*/
/*@ requires let x4 = ((i32) p); @*/
/*@ requires (x1 > 0u64) && (x2 > 0u32) && (x3 > 0i64) && (x4 > 0i32); @*/
{
  return 1;
}
