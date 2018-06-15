/* Test from Jacques-Henri Jourdan and Francois Pottier TOPLAS 2017:
 * "A simple, possibly correct LR parser for C11"
 */
typedef int T, U;
int x;
void f(void) {
  if (sizeof(enum {T}))
    x = sizeof(enum {U}) + T;
  else {
    U u = (int)T;
  }
  switch (sizeof(enum {U})) x = U;
  T t; U u;
}
