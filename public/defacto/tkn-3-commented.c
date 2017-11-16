#include <stdio.h>
#include <stdlib.h>

typedef unsigned long  word_t;

//PS: kfree_list is supposed to point to a linked list of 1024-byte free blocks,often adjacent, with a word_t* pointer to the next at the start of each. 
word_t* kfree_list;

//PS: what are the preconditions on size?  
void * alloc(word_t size) {
  word_t *prev, *curr, *tmp;
  word_t i;
  //PS: clip size to at least 1024
  size = size >= 1024 ? size : 1024;
  //PS: walk along the linked list 
  for (prev = (word_t*) &kfree_list, curr = kfree_list;
       curr;
       prev = curr, curr = (word_t*) *curr) {
    //PS: if curr is size-aligned (that seems very strong?) then
    if (!((word_t) curr & (size - 1))) {
      //PS: tmp is the next block after curr (or 0 if the end)
      tmp = (word_t*) *curr;
      //PS:  now check there's a sufficient adjacent sequence of blocks 
      for (i = 1; tmp && (i < size / 1024); i++) {
        if ((word_t) tmp != ((word_t) curr + 1024*i)) {
          tmp = 0;
          break;
        };
        tmp = (word_t*) *tmp;
      }
      //PS: tmp is now either the next free block or zero (if we didn't find a sequence)
      if (tmp) {
        //PS: cut this sequence of adjacent blocks out of the list
        *prev = (word_t) tmp;
        //PS: zero the current block, in word_t units
        for (i = 0; i < (size / sizeof(word_t)); i++) {
          /** AUXUPD:
              (ptr-safe (´curr +p ´i) ´d, ptr-tag (´curr +p ´i) ´d) */
          curr[i] = 0;
        }
        //PS: return the current block
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
    r = (void*)((((word_t)r) & ~((word_t)(1024-1))) + (word_t)1024);
  // initialise the internal next-block pointers
  int i;
  for (i=0; i < n-1; i++)
    *((word_t *)((word_t)r+i*1024)) = (word_t)r+(i+1)*1024;
  // initialise the end-of-list next-block pointer
  *(word_t *)(word_t)r+(n-1)*1024) = 0;
  // initialise the head of list
  kfree_list = (word_t *)r;
  print_free_list(kfree_list);  

  // try two allocations
  void *a, *b, *c;
  a = alloc(2048); // should succeed
  b = alloc(2048); // should succeed
  c = alloc(65536);// should fail
  printf("a=%p b=%p c=%p\n",a,b,c);

  print_free_list(kfree_list); 

}
