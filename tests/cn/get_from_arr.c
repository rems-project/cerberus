
/* originally made by minimising a problematic case from memcpy.c */


char
get_from_arr (char *in_arr)
/*@ requires take IA = each (integer j; 0 <= j && j < 10)
  {Owned<char>(in_arr + j)} @*/
/*@ ensures take IA2 = each (integer j; 0 <= j && j < 10)
  {Owned<char>(in_arr + j)} @*/
{
  char c;

  /*@ extract Owned<char>, 4; @*/
  /*@ instantiate good<char>, 4; @*/
  c = in_arr[4];

  return c;
}

