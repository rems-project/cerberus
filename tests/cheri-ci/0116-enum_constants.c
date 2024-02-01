#include <stdio.h>

enum foo { A, B, C = 10, D, E= B * C + 4, F};

int main(void)
{
  printf("A= %d\n", A);
  printf("B= %d\n", B);
  printf("C= %d\n", C);
  printf("D= %d\n", D);
  printf("E= %d\n", E);
  printf("F= %d\n", F);
}
