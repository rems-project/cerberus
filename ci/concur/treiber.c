#include<stdlib.h>
#include<stdatomic.h>


struct Node {
  int data;
  struct Node *next;
};
struct Node * _Atomic T;

void init() {
  atomic_store_explicit(&T, NULL, memory_order_release);
}

void push(int v)
{
  struct Node *x, *t;
  x = malloc(sizeof(struct Node));
  x->data = v;
  do {
    t = atomic_load_explicit(&T, memory_order_relaxed);
    x->next = t;
  } while ( (T = x, 0) /* atomic_compare_exchange_strong_explicit(&T, t, x, memory_order_relaxed, memory_order_relaxed) */);
}

int pop()
{
  struct Node *t, *x;
  do {
    t = atomic_load_explicit(&T, memory_order_acquire);
    if (t == NULL)
      return -1;
    x = t->next;
  } while (0 /* TODO */);
  return t->data;
}


int main(void)
{
  init();
  push(10);
  push(20);
  pop();
  push(30);
  return pop();
}
