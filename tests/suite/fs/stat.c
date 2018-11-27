#include <fcntl.h>
#include <unistd.h>
#include <stdio.h>
#include <sys/stat.h>

int main()
{
  int fd = open("testfile.txt", O_RDWR | O_CREAT);
  char *s = "MY STR\0ING";
  write (fd, s, 10);
  close(fd);
  struct stat st;
  stat("testfile.txt", &st);
  printf("%d %llu %hu %hu %u %u %d %lld\n", st.st_dev, st.st_ino, st.st_mode, st.st_nlink, st.st_uid, st.st_gid, st.st_rdev, st.st_size);
}
