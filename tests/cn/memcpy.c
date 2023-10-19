void
memcpy (char *dst, char *src, int n)
/*@ requires take dstStart = each (integer j; 0 <= j && j < n) {Owned(dst + j)} @*/
/*@ requires take srcStart = each (integer j; 0 <= j && j < n) {Owned(src + j)} @*/
/*@ ensures take dstEnd = each (integer j; 0 <= j && j < n) {Owned(dst + j)} @*/
/*@ ensures take srcEnd = each (integer j; 0 <= j && j < n) {Owned(src + j)} @*/
/*@ ensures srcEnd == srcStart @*/
/*@ ensures each (integer k; 0 <= k && k < n) {dstEnd[k] == srcStart[k]} @*/
{
  int i;
  for (i = 0; i < n; i++)
  /*@ inv take dstInv = each (integer j; 0 <= j && j < n) {Owned(dst + j)} @*/
  /*@ inv take srcInv = each (integer j; 0 <= j && j < n) {Owned(src + j)} @*/
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
