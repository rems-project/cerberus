

/* Simple demo of a kind of situation where ownership is obtained via an array
   that encloses an object passed by pointer. This kind of step is required by
   the buddy-allocator proof. */

int *global_array;

enum {
  global_array_width = 42,
};

/*@ function (integer) global_array_width () @*/

static inline int get_global_array_width_for_cn (void)
/*@ cn_function global_array_width @*/
{
  return global_array_width;
}

/*@
predicate (map<integer, integer>) Global_Array (pointer p)
{
  take Arr = each (integer i; 0 <= i && i < global_array_width ())
    { Owned(array_shift<int>(p, i)) };
  return Arr;
}
@*/

void set_a_pointer(int *p, int x)
/*@ accesses global_array @*/
/*@ requires take Arr = Global_Array(global_array) @*/
/*@ requires let offs = ((integer)p - (integer)global_array) @*/
/*@ requires mod(offs, sizeof<int>) == 0 @*/
/*@ requires let idx = (offs / sizeof<int>) @*/
/*@ requires 0 <= idx && idx < global_array_width () @*/
/*@ ensures take Arr2 = Global_Array(global_array) @*/
{
  /*@ extract Owned<int>, idx; @*/
  *p = x;
}

