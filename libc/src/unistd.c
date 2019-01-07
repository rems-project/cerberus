#include "unistd.h"

// TODO: isatty
int isatty (int fd)
{
  return 0;//return (fd == 1 || fd == 2);
}

static void __procfdname(char *buf, unsigned fd)
{
  unsigned i, j;
  for (i=0; (buf[i] = "/proc/self/fd/"[i]); i++);
  if (!fd) {
    buf[i] = '0';
    buf[i+1] = 0;
    return;
  }
  for (j=fd; j; j/=10, i++);
  buf[i] = 0;
  for (; fd; fd/=10) buf[--i] = '0' + fd%10;
}

int fchown(int fd, uid_t uid, gid_t gid)
{
  /*
  int ret = __syscall(SYS_fchown, fd, uid, gid);
  if (ret != -EBADF || __syscall(SYS_fcntl, fd, F_GETFD) < 0)
    return __syscall_ret(ret);
  */

  char buf[15+3*sizeof(int)];
  __procfdname(buf, fd);
  return chown(buf, uid, gid);
}
