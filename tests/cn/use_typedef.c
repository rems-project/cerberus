

typedef unsigned long long x_type;

/*@
function (x_type) make_x (x_type x)
  { x }
@*/

int test (x_type x)
/*@ requires make_x (x) == x; @*/
{
  return 0;
}

