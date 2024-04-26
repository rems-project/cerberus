
/* based on a problematic example from linux kvm/pgtable.c */

struct str {
  int x;
  int y;
};

int f (int x)
/*@ requires (0i32 <= x) && (x < 200i32); @*/
{
  struct str str_inst = {
    .x = x + 2,
    .y = str_inst.x + 3,
  };

  return str_inst.y;
}

