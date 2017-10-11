/* Test from Jacques-Henri Jourdan and Francois Pottier TOPLAS 2017:
 * "A simple, possibly correct LR parser for C11"
 */
typedef int T;
void f(void) {
  int x = (int)(enum {T})1;
  x = (int)T; // T should be an enum constant
}
