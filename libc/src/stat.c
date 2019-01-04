#include "sys/stat.h"

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

int fchmod(int fd, mode_t mode)
{
  /*
  int ret = __syscall(SYS_fchmod, fd, mode);
  if (ret != -EBADF || __syscall(SYS_fcntl, fd, F_GETFD) < 0)
    return __syscall_ret(ret);
  */

  char buf[15+3*sizeof(int)];
  __procfdname(buf, fd);
  return chmod(buf, mode);
}

int utimensat(int fd, const char *path, const struct timespec times[2], int flags)
{
  /* TODO:
  int r = __syscall(SYS_utimensat, fd, path, times, flags);
#ifdef SYS_futimesat
  if (r != -ENOSYS || flags) return __syscall_ret(r);
  struct timeval *tv = 0, tmp[2];
  if (times) {
    int i;
    tv = tmp;
    for (i=0; i<2; i++) {
      if (times[i].tv_nsec >= 1000000000ULL) {
        if (times[i].tv_nsec == UTIME_NOW &&
            times[1-i].tv_nsec == UTIME_NOW) {
          tv = 0;
          break;
        }
        if (times[i].tv_nsec == UTIME_OMIT)
          return __syscall_ret(-ENOSYS);
        return __syscall_ret(-EINVAL);
      }
      tmp[i].tv_sec = times[i].tv_sec;
      tmp[i].tv_usec = times[i].tv_nsec / 1000;
    }
  }

  r = __syscall(SYS_futimesat, fd, path, tv);
  if (r != -ENOSYS || fd != AT_FDCWD) return __syscall_ret(r);
  r = __syscall(SYS_utimes, path, tv);
#endif
  return __syscall_ret(r);
  */
  return 0;
}
