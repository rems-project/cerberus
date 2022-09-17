#include <stdio.h>

int main()
{
   char a;
   short b;

   printf("%lu %lu\n", sizeof(char), sizeof(a));
   printf("%lu %lu\n", sizeof(short), sizeof(b));

   return 0;
}

/* vim: set expandtab ts=4 sw=3 sts=3 tw=80 :*/
