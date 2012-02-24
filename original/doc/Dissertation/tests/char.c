#include <stdio.h>

char global[10];

char *unary(unsigned short s) {
  if (s % 1) printf("True.\n"); else printf("False.\n");
  char *p = (s % 2)? global : NULL;
  for (int i=0; i < s; i++) p[i]='1';
  p[s]='\0';
  return p;
}

int main(void) {
  printf("%s\n", /*((void)*/ unary(7)/*, global)*/); //What does this print?
  return 0;
}
