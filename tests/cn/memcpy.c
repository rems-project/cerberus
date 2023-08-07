


void
naive_memcpy (char *in_arr, char *out_arr, int i)
/*@ requires take IA = each (integer j; 0 <= j && j < i) {Owned(in_arr + (j * sizeof<char>))} @*/
/*@ requires take OA = each (integer j; 0 <= j && j < i) {Owned(out_arr + (j * sizeof<char>))} @*/
/*@ requires 0 <= i @*/
/*@ ensures take IA2 = each (integer j; 0 <= j && j < i) {Owned(in_arr + (j * sizeof<char>))} @*/
/*@ ensures take OA2 = each (integer j; 0 <= j && j < i) {Owned(out_arr + (j * sizeof<char>))} @*/
/*@ ensures IA2 == IA @*/
/*@ ensures each (integer k; 0 <= k && k < i) {OA2[k] == IA[k]} @*/
{
  int j;

  for (j = 0; j < i; j++)
  /*@ inv take IA3 = each (integer k; 0 <= k && k < i) {Owned(in_arr + (k * sizeof<char>))} @*/
  /*@ inv take OA3 = each (integer k; 0 <= k && k < i) {Owned(out_arr + (k * sizeof<char>))} @*/
  /*@ inv IA3 == IA @*/
  /*@ inv each (integer k; 0 <= k && k < j) {OA3[k] == IA[k]} @*/
  /*@ inv 0 <= j && j <= i @*/
  /*@ inv i == {i}@start @*/
  /*@ inv {in_arr} unchanged @*/
  /*@ inv {out_arr} unchanged @*/
  {
    /*@ extract Owned<char>, j; @*/
    out_arr[j] = in_arr[j];
  }

}

