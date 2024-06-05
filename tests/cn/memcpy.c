void
naive_memcpy (char *dst, char *src, int n)
/*@ requires take dstStart = each (i32 j; 0i32 <= j && j < n)
                                  {Owned(array_shift(dst, j))};
             take srcStart = each (i32 j; 0i32 <= j && j < n)
                                  {Owned(array_shift(src, j))};
    ensures take dstEnd = each (i32 j; 0i32 <= j && j < n)
                               {Owned(array_shift(dst, j))};
            take srcEnd = each (i32 j; 0i32 <= j && j < n)
                               {Owned(array_shift(src, j))};
            srcEnd == srcStart;
            each (i32 k; 0i32 <= k && k < n) {dstEnd[k] == srcStart[k]};
@*/
{
  int i;
  for (i = 0; i < n; i = i + 1)
  /*@ inv take dstInv = each (i32 j; 0i32 <= j && j < n)
                             {Owned(array_shift(dst, j))};
          take srcInv = each (i32 j; 0i32 <= j && j < n)
                             {Owned(array_shift(src, j))};
          srcInv == srcStart;
          each (i32 j; 0i32 <= j && j < i) {dstInv[j] == srcStart[j]};
          0i32 <= i;
          {dst} unchanged;
          {src} unchanged;
          {n} unchanged; @*/
  {
    /*@ extract Owned<char>, (i32)i; @*/
    /*@ instantiate good<char>, (i32)i; @*/
    dst[i] = src[i];
  }
}

int main(void) {
  char *src = "hello";
  char dst[5];
  naive_memcpy(dst, src, 5);
  return 0;
}