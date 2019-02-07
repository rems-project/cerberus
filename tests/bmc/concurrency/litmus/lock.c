// lock
#include <threads.h>
int main() {
  mtx_t m;
  int r1;
  mtx_init(&m);
  {-{ {
    mtx_lock(&m);
    x = x + 1;
    x = x + 1
    mtx_unlock(&m);
  } ||| {
    mtx_lock(&m);
    r1 = x;
    mtx_unlock(&m);
  } }-};
  assert(!(r1 == 1));
  return r1;
}
