void
memcpy (char *dst, char *src, int n)
/*@ requires take dstStart = each (i32 j; 0i32 <= j && j < n)
    {Owned(array_shift(dst, j))} @*/
/*@ requires take srcStart = each (i32 j; 0i32 <= j && j < n)
    {Owned(array_shift(src, j))} @*/
/*@ ensures take dstEnd = each (i32 j; 0i32 <= j && j < n)
    {Owned(array_shift(dst, j))} @*/
/*@ ensures take srcEnd = each (i32 j; 0i32 <= j && j < n)
    {Owned(array_shift(src, j))} @*/
/*@ ensures srcEnd == srcStart @*/
/*@ ensures each (i32 k; 0i32 <= k && k < n) {dstEnd[k] == srcStart[k]} @*/
{
  int i;
  for (i = 0; i < n; i = i + 1)
  /*@ inv take dstInv = each (i32 j; 0i32 <= j && j < n)
    {Owned(array_shift(dst, j))} @*/
  /*@ inv take srcInv = each (i32 j; 0i32 <= j && j < n)
    {Owned(array_shift(src, j))} @*/
  /*@ inv srcInv == srcStart @*/
  /*@ inv each (i32 j; 0i32 <= j && j < i) {dstInv[j] == srcStart[j]} @*/
  /*@ inv 0i32 <= i @*/
  /*@ inv {dst} unchanged @*/
  /*@ inv {src} unchanged @*/
  /*@ inv {n} unchanged @*/
  {
    /*@ extract Owned<char>, (i32)i; @*/
    /*@ instantiate good<char>, (i32)i; @*/
    dst[i] = src[i];
  }
}
