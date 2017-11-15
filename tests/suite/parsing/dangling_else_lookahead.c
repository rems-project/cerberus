/* Test from Jacques-Henri Jourdan and Francois Pottier TOPLAS 2017:
 * "A simple, possibly correct LR parser for C11"
 */
typedef int T;
void f(void) {
  for (int T;;)
    if (1);
  T x;
  x = 0;
}
