

/* Simple demo of a kind of situation where ownership is obtained via an array
   that encloses an object passed by pointer. This kind of step is required by
   the buddy-allocator proof. */

int *global_array;

enum {
  global_array_width = 42,
};

/*@ function (i32) global_array_width () @*/

static inline int get_global_array_width_for_cn (void)
/*@ cn_function global_array_width @*/
{
  return global_array_width;
}

/*@
predicate (map<i32, i32>) Global_Array (pointer p)
{
  take Arr = each (i32 i; 0i32 <= i && i < global_array_width ())
    { Owned<int>(p + (i * ((i32) (sizeof<int>)))) };
  return Arr;
}
@*/

void set_a_pointer(int *p, int x)
/*@ accesses global_array @*/
/*@ requires take Arr = Global_Array(global_array) @*/
/*@ requires let offs = ((u64)p - (u64)global_array) @*/
/*@ requires mod(offs, sizeof<int>) == 0u64 @*/
/*@ requires let idx = (offs / sizeof<int>) @*/
/*@ requires 0u64 <= idx && idx < ((u64) (global_array_width ())) @*/
/*@ ensures take Arr2 = Global_Array(global_array) @*/
{
  /*@ extract Owned<int>, idx; @*/
  *p = x;
}

