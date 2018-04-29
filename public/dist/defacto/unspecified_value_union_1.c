#include <stdio.h>
typedef union { int i; float f; } un;
int main() {
  un u;
  int j;
  u.i = j;
  // does u contain an unspecified union value, or an 
  // i member that itself has an unspecified int value?
  int k;
  float g;
  k = *((int*)&u);  //does this have defined behaviour?
  g = *((float*)&u);//does this have undefined behaviour?
}
