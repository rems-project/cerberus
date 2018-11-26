#ifndef _SYS_UIO_H_
#define _SYS_UIO_H_

#include <sys/types.h>
#include <unistd.h>
#include <limits.h>
#include <assert.h>
#include <stdlib.h>

struct iovec {
  void *iov_base;
  size_t iov_len;
};

ssize_t readv (int fd, const struct iovec * vec, int count)
{
  int res = 0;
  for (int i = 0; i < count; i++) {
    res += read (fd, vec[i].iov_base, vec[i].iov_len);
  }
  return res;
}

ssize_t writev (int fd, const struct iovec * vec, int count)
{
  int res = 0;
  for (int i = 0; i < count; i++) {
    res += write(fd, vec[i].iov_base, vec[i].iov_len);
  }
  return res;
}


#endif
