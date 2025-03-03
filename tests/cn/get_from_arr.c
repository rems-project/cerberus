
/* originally made by minimising a problematic case from memcpy.c */


char
get_from_arr (char *in_arr)
/*@ requires take IA = each (i32 j; 0i32 <= j && j < 10i32)
  {Owned<char>(in_arr + j)};
    ensures take IA2 = each (i32 j; 0i32 <= j && j < 10i32)
  {Owned<char>(in_arr + j)}; @*/
{
  char c;

  /*@ extract Owned<char>, 4i32; @*/
  /*@ instantiate good<char>, 4i32; @*/
  c = in_arr[4];

  return c;
}

int main(void)
/*@ trusted; @*/
{
  char *str = "hello";
  char c = get_from_arr(str);
}
