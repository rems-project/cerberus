#include <stdio.h>
#include <stdlib.h>

typedef unsigned long  word_t;

word_t* kfree_list;

void * alloc(word_t size) {
  word_t *prev, *curr, *tmp;
  word_t i;
  size = size >= 1024 ? size : 1024;
  for (prev = (word_t*) &kfree_list, curr = kfree_list;
       curr;
       prev = curr, curr = (word_t*) *curr) {
    if (!((word_t) curr & (size - 1))) {
      tmp = (word_t*) *curr;
      for (i = 1; tmp && (i < size / 1024); i++) {
        if ((word_t) tmp != ((word_t) curr + 1024*i)) {
          tmp = 0;
          break;
        };
        tmp = (word_t*) *tmp;
      }
      if (tmp) {
        *prev = (word_t) tmp;
        for (i = 0; i < (size / sizeof(word_t)); i++) {
          curr[i] = 0;
        }
        return curr;
      }
    }
  }
  return 0;
}

void print_free_list(word_t* p) {
  word_t* q = p;
  printf("free list: ");
  while (q != NULL) {
    printf("%p ",(void*)q);
    q = (word_t*) *q;
  }
  printf("%p\n",(void*)q);
}

int main() {
  int n=10; // number of blocks
  void *r = malloc(1024*(n+1));
  // crudely force r to be 1024-byte-aligned
  if (((word_t)r & (1024-1)) != 0) 
    r = (void*)((((word_t)r) & ~((word_t)(1024-1)))
                + (word_t)1024);
  // initialise the internal next-block pointers
  int i;
  for (i=0; i < n-1; i++)
    *((word_t *)((word_t)r+i*1024)) 
      = (word_t)r+(i+1)*1024;
  *(word_t *)((word_t)r+(n-1)*1024) = 0;
  kfree_list = (word_t *)r;
  // try some allocations
  print_free_list(kfree_list);  
  void *a, *b, *c;
  a = alloc(1024); // should succeed
  b = alloc(2048); // should succeed
  c = alloc(65536);// should fail
  printf("a=%p b=%p c=%p\n",a,b,c);
  print_free_list(kfree_list); 
}
