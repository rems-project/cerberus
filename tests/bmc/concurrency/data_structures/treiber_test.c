#include <stdlib.h>
#include <stdatomic.h>

struct Node {
  int data;
  struct Node *next; };
struct Node * _Atomic T;
void init() {
  atomic_store_explicit(&T, NULL, memory_order_release);
}

void push(struct Node *x, int v) {
   struct Node *t;
   x->data = v;

   t = atomic_load_explicit(&T, memory_order_relaxed);
   x->next = t;
   __BMC_ASSUME((atomic_compare_exchange_strong_explicit(&T, &t, x, 
                memory_order_acq_rel, memory_order_relaxed)));
}

int pop() {
  struct Node *t, *x;
  t = atomic_load_explicit(&T, memory_order_acquire);
  if (t == NULL) 
    return -1;
  x = t->next;
  __BMC_ASSUME((atomic_compare_exchange_strong_explicit(&T, &t, x, 
               memory_order_acq_rel, memory_order_relaxed)));
  return t->data;
}

int main(void)
{
    struct Node a;
//    struct Node b;
    int ret;
    init();

    {-{ {
            struct Node *t;
            a.data = 42;
            t = atomic_load_explicit(&T, memory_order_relaxed);
            a.next = t;
            __BMC_ASSUME((atomic_compare_exchange_strong_explicit(&T, &t, &a, 
                         memory_order_acq_rel, memory_order_relaxed)));

//          push(&a, 42);
//          push(&b, 88);
        }
    ||| {
            struct Node *t, *x;
            t = atomic_load_explicit(&T, memory_order_acquire);
            __BMC_ASSUME(t != NULL); 
            //__BMC_ASSUME(t == NULL);
            if (t == NULL) {
              ret = -1;
            } else {
              x = t->next;
              __BMC_ASSUME((atomic_compare_exchange_strong_explicit(&T, &t, x, 
                           memory_order_acq_rel, memory_order_relaxed)));
              ret = t->data;
            }
              
//        ret = pop();
        }
    }-}
    return ret;
}
