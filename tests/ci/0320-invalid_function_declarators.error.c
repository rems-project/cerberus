// the last two declarations of 'x' are in the same scope
struct S {
  int (*f)(int x, int (*g)(int x, int x));
};