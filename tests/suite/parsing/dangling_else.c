/* Test from Jacques-Henri Jourdan and Francois Pottier TOPLAS 2017:
 * "A simple, possibly correct LR parser for C11"
 */
int f(void) {
  if (0)
    if (1) return 1;
    else return 0;
  return 1;
}
