#include <stdio.h>

int main()
{
   char a;
   int b;
   double c;

   printf("%lu\n", sizeof(a));
   printf("%lu\n", sizeof(b));
   printf("%lu\n", sizeof(c));

   printf("%lu\n", sizeof(!a));

   return 0;
}

/* vim: set expandtab ts=4 sw=3 sts=3 tw=80 :*/
