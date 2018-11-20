// taken from https://github.com/mit-pdos/xv6-public/blob/master/ln.c
#include <stdlib.h>
#include <stdio.h>
#include <unistd.h>
int
main(int argc, char *argv[])
{
  if(argc != 3){
    printf("Usage: ln old new\n");
    exit(1);
  }
  if(link(argv[1], argv[2]) < 0)
    printf("link %s %s: failed\n", argv[1], argv[2]);
  exit(0);
}
