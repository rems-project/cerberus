#include <fcntl.h>
#include <sys/stat.h>
#include <dirent.h>
#include <unistd.h>
#include <stdio.h>
#include <assert.h>
#include <stdlib.h>
#include <errno.h>

void create(const char *name)
{
  int fd = open(name, O_RDWR | O_CREAT);
  write (fd, "SOME CONTENT", 12);
  close(fd);
}

int main() {
  assert (errno == 0);

  mkdir("mydir", 1);
  chdir("mydir");
  create("file1");
  create("file2");
  create("file3");
  chdir("..");

  DIR *dir = opendir("mydir");

  struct dirent * d= readdir(dir);
  printf("%s\n", d->d_name);
  d = readdir(dir);
  printf("%s\n", d->d_name);
  d = readdir(dir);
  printf("%s\n", d->d_name);
  d = readdir(dir);
  printf("%s\n", d->d_name);
  d = readdir(dir);
  printf("%s\n", d->d_name);
  d = readdir(dir);
  assert(d == NULL);

  rewinddir(dir);

  d = readdir(dir);
  printf("%s\n", d->d_name);
  d = readdir(dir);
  printf("%s\n", d->d_name);
  d = readdir(dir);
  printf("%s\n", d->d_name);
  d = readdir(dir);
  printf("%s\n", d->d_name);
  d = readdir(dir);
  printf("%s\n", d->d_name);
  d = readdir(dir);
  assert(d == NULL);

  closedir(dir);

  assert (readdir(dir) == NULL && errno != 0);
}