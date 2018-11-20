#include <fcntl.h>
#include <unistd.h>
#include <stdio.h>

int main()
{
  int fd = open("testfile.txt", O_RDWR | O_CREAT);
  char *s = "MY STRING";
  write (fd, s, 9);
  close(fd);

  int fd2 = open("testfile.txt", O_RDONLY);
  char buf[20];
  int n = read (fd2, buf, 1000);
  printf("> %s\n", buf);

  return n;
}
