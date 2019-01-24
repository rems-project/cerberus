#include <string.h>
#include <stdio.h>
#include <stdint.h>

// If f(A, B + 4) is given, and integer representation of A and B + 4
// are the same, c1 == c2 in the loop becomes true,
// so arr3 = arr1. Hence r = A, and *A should be 10.
// However, if compiled with -O3, *A is still 1.
void store_10_to_p(int *p, int *q) {
  unsigned char arr1[8];
  unsigned char arr2[8];
  unsigned char arr3[8];
  // Type punning with char* is allowed.
  memcpy((unsigned char*)arr1, (unsigned char *)&p, sizeof(p));
  memcpy((unsigned char*)arr2, (unsigned char *)&q, sizeof(q));
  // Now arr1 is p, arr2 is q.

  for (int i = 0; i < sizeof(q); i++) {
    int c1 = (int)arr1[i], c2 = (int)arr2[i];
    // Note that c1 == c2 is a comparison between _integers_ (not pointers).
    if (c1 == c2)
      // Always true if p and q have same integer representation.
      arr3[i] = arr1[i];
    else
      arr3[i] = arr2[i];
  }
  // Now arr3 is equivalent to arr1, which is p.
  int *r;
  memcpy(&r, (unsigned char *)arr3, sizeof(r));
  // Now r is p.
  *p = 1;
  *r = 10;
}

int main() {
  int B[4], A[4];
  printf("%p %p\n", (void*)A, (void*)&B[4]);
  if ((uintptr_t)A == (uintptr_t)&B[4]) {
    store_10_to_p(A, &B[4]);
    printf("%d\n", A[0]);
  }
  return 0;
}