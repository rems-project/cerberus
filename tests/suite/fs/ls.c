// taken from https://github.com/mit-pdos/xv6-public/blob/master/ls.c
// modified to POSIX
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <dirent.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <unistd.h>

#define DIRSIZ 20

char*
fmtname(char *path)
{
  static char buf[DIRSIZ+1];
  char *p;

  // Find first character after last slash.
  for(p=path+strlen(path); p >= path && *p != '/'; p--)
    ;
  p++;

  // Return blank-padded name.
  if(strlen(p) >= DIRSIZ)
    return p;
  memmove(buf, p, strlen(p));
  memset(buf+strlen(p), ' ', DIRSIZ-strlen(p));
  return buf;
}

void
ls(char *path)
{
  char buf[512], *p;
  int fd;
  struct dirent de;
  struct stat st;

  if((fd = open(path, 0)) < 0){
    printf("ls: cannot open %s\n", path);
    return;
  }

  if(fstat(fd, &st) < 0){
    printf("ls: cannot stat %s\n", path);
    close(fd);
    return;
  }

  switch(st.st_mode){
  case S_IFREG: // T_FILE:
    printf("%s %d %d %d\n", fmtname(path), st.st_mode, st.st_ino, st.st_size);
    break;

  case S_IFDIR: // T_DIR:
    if(strlen(path) + 1 + DIRSIZ + 1 > sizeof buf){
      printf( "ls: path too long\n");
      break;
    }
    strcpy(buf, path);
    p = buf+strlen(buf);
    *p++ = '/';
    while(read(fd, &de, sizeof(de)) == sizeof(de)){
      if(de.d_ino == 0)
        continue;
      memmove(p, de.d_name, DIRSIZ);
      p[DIRSIZ] = 0;
      if(stat(buf, &st) < 0){
        printf("ls: cannot stat %s\n", buf);
        continue;
      }
      printf("%s %d %d %d\n", fmtname(buf), st.st_mode, st.st_ino, st.st_size);
    }
    break;
  }
  close(fd);
}

int
main(int argc, char *argv[])
{
  int i;

  if(argc < 2){
    ls(".");
    exit(1);
  }
  for(i=1; i<argc; i++)
    ls(argv[i]);
  exit(0);
}
