
int
test_cast_loc_to_various (int *p)
/*@
requires
    let p_u64 = (u64)p;
    let p_u32 = (u32)p;
    let p_i64 = (i64)p;
    let p_i32 = (i32)p;
    p_u64 <= MAXu64() - 3u64;
    p_u32 <= MAXu32() - 3u32;
    MINi64() <= p_i64 && p_i64 <= MAXi64() - 3i64;
    MINi32() <= p_i32 && p_i32 <= MAXi32() - 3i32;
@*/
{
  return 1;
}

int main(void)
{
  int p[1] = {0};
  test_cast_loc_to_various(p);
}
