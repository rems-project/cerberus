// from https://github.com/mit-pdos/xv6-public/blob/master/mkdir.c
#include <sys/stat.h>
#include <stdio.h>
#include <stdlib.h>

int
main(int argc, char *argv[])
{
  int i;

  if(argc < 2){
    printf("Usage: mkdir files...\n");
    exit(0);
  }

  for(i = 1; i < argc; i++){
    if(mkdir(argv[i], 1) < 0){
      printf("mkdir: %s failed to create\n", argv[i]);
      break;
    }
  }
}
