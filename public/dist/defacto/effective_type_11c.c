  
#include <new>
extern "C" void abort();

typedef int A;
typedef float B;

B *qq;

void foo(A *p, A *q, long unk) {
   for (long i = 0; i < unk; ++i) {
      ++*p;
      qq = new (static_cast<void *>(&q[i])) B(42);
      // Note: the following is a TBAA violation.
      //qq = &(*reinterpret_cast<B *>(static_cast<void *>(&q[i])) = B(42));
   }
}

void (*volatile fp)(A *, A *, long);

int main(void) {
   union { A x; B f; } u = { 0 };
   fp = foo;
   fp(&u.x, &u.x, 1);
   if (*qq != 42) abort();
}
