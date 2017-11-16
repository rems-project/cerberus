#include <stdio.h>
typedef unsigned long  word_t;

word_t reverse(word_t *i) {
  word_t j = 0;
  while (i) {
    word_t *k = (word_t*)*i;
    *i = j;
    j = (word_t)i;
    i = k;
  }
  return j;
}

int main() {
  word_t a[3];
  a[0] = (word_t) &a[1];
  a[1] = (word_t) &a[2];
  a[2] = (word_t) 0;
  word_t b;
  printf("a[0]=%lu a[1]=%lu a[2]=%lu\n",
         a[0],a[1],a[2]);
  b = reverse(a);
  printf("a[0]=%lu a[1]=%lu a[2]=%lu b=%lu\n",
         a[0],a[1],a[2],b);
}
