#include <stdio.h>
int i = 0, a[2] = {0,0};
int f(void) { 
  i++; 
  return i; }
/* will print either 0 or 1 */
int main(void) { 
  a[i] = f(); 
  printf("%i\n",a[0]); }
