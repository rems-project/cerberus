#include <stdio.h>
int* f() { 
  int a; 
  return &a; }
int* g() { 
  int a; 
  return &a; }
int main() { 
  _Bool b = (f() == g()); // can this be true?
  printf("(f()==g())=%s\n",b?"true":"false"); 
}
