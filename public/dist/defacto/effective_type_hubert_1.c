#include <stdlib.h>
#include <string.h>

typedef struct A { int x, y; } A;
typedef struct B { int x, y; } B;

//__attribute__((__noinline__, __weak__))
B *newB(void *p) {
    static const B b = { 0 };
    return (B *)memcpy(p, &b, sizeof b);
}

int main(void) {
  static const A a = { 0 };

  A *const ap = (A *)malloc(sizeof a);
  memcpy(ap, &a, sizeof a);

  B *const bp = newB(ap);
  bp->y = 42;
  ap->y = 0; // Hubert says: I think this should be UB.
             // Both Clang and GCC will not expect
             // this to alias bp->y under TBAA.
  return bp->y; // 42?
}
