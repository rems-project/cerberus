/* Test from Jacques-Henri Jourdan and Francois Pottier TOPLAS 2017:
 * "A simple, possibly correct LR parser for C11"
 */
typedef signed int T;
struct S {
  unsigned T:3;
  const T:3;
};
