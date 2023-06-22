void
memcpy (char *dst, char *src, int n)
/*@ requires take dstStart = each (integer j; 0 <= j && j < n) {Owned(dst + (j * sizeof<char>))} @*/
/*@ requires take srcStart = each (integer j; 0 <= j && j < n) {Owned(src + (j * sizeof<char>))} @*/
/*@ ensures take dstEnd = each (integer j; 0 <= j && j < n) {Owned(dst + (j * sizeof<char>))} @*/
/*@ ensures take srcEnd = each (integer j; 0 <= j && j < n) {Owned(src + (j * sizeof<char>))} @*/
/*@ ensures srcEnd == srcStart @*/
/*@ ensures each (integer k; 0 <= k && k < n) {dstEnd[k] == srcStart[k]} @*/
{
  int i;
  for (i = 0; i < n; i++)
  /*@ inv take dstInv = each (integer j; 0 <= j && j < n) {Owned(dst + (j * sizeof<char>))} @*/
  /*@ inv take srcInv = each (integer j; 0 <= j && j < n) {Owned(src + (j * sizeof<char>))} @*/
  /*@ inv srcInv == srcStart @*/
  /*@ inv each (integer j; 0 <= j && j < i) {dstInv[j] == srcStart[j]} @*/
  /*@ inv 0 <= i @*/
  /*@ inv {dst} unchanged @*/
  /*@ inv {src} unchanged @*/
  /*@ inv {n} unchanged @*/
  {
    /*@ extract Owned<char>, i; @*/
    /*@ instantiate good<char>, i; @*/
    dst[i] = src[i];
  }
}