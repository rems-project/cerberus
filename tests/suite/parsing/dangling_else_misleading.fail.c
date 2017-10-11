/* Test from Jacques-Henri Jourdan and Francois Pottier TOPLAS 2017:
 * "A simple, possibly correct LR parser for C11"
 */
typedef int T;
void f(void) {
  if(1)
    for (int T; ;)
      if (1) {}
      else {
        T x;
      }
}
