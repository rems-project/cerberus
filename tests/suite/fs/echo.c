// from https://github.com/mit-pdos/xv6-public/blob/master/echo.c
#include <stdio.h>

int
main(int argc, char *argv[])
{
  for(int i = 1; i < argc; i++)
    printf("%s%s", argv[i], i+1 < argc ? " " : "\n");
}
