#include <fcntl.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <unistd.h>
#include <stdio.h>

int creat(const char *path, mode_t mode) {
  return open(path, O_CREAT | O_TRUNC | O_WRONLY, mode);
}

int main() {
  const char * fn="readlink.file";
  const char * sl="readlink.symlink";
  char buf[30];
  int  fd;

  if ((fd = creat(fn, 0)) < 0)
    perror("creat() error");
  else {
    close(fd);
    if (symlink(fn, sl) != 0)
      perror("symlink() error");
    else {
      if (readlink(sl, buf, sizeof(buf)) < 0)
        perror("readlink() error");
      else printf("readlink() returned '%s' for '%s'\n", buf, sl);
      unlink(sl);
    }
    unlink(fn);
  }
}
