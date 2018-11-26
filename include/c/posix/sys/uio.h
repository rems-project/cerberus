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
  // TODO: this is a hack, assuming IOV_MAX = 1
  assert (IOV_MAX == 1 && count == 1 && vec != NULL);
  return read (fd, vec->iov_base, vec->iov_len);
}

ssize_t writev (int fd, const struct iovec * vec, int count)
{
  // TODO: this is a hack, assuming IOV_MAX = 1
  assert (IOV_MAX == 1 && count == 1 && vec != NULL);
  return write (fd, vec->iov_base, vec->iov_len);
}


#endif
