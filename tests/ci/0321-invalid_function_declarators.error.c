// the first and last declarations of 'x' are in the same scope
struct S {
  int (*f)(int x, int (*g)(int x), int x);
};