#include<stdio.h>
#include<limits.h>

void toBinary (int n)
{
  unsigned char *c = (unsigned char *)&n;
  for (int i=sizeof(int); i; (i--, c++)) {
    unsigned char mask = 1;
    for (int j=0; j<CHAR_BIT; (j++, mask <<= 1)) {
      printf("%c", *c & mask ? '1' : '0');
    }
  }
  printf("\n");
}

int main(void)
{
  int x = 2;
  unsigned char *c;
  c = (unsigned char *)&x;
  c+=2;
  toBinary(x);
  *c = 42;
  toBinary(x);

  return 0;
}
