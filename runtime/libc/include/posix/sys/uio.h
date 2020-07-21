#ifndef _SYS_UIO_H_
#define _SYS_UIO_H_

#include <sys/types.h>
#include <stdlib.h>

struct iovec {
  void *iov_base;
  size_t iov_len;
};

ssize_t readv (int fd, const struct iovec * vec, int count);
ssize_t writev (int fd, const struct iovec * vec, int count);

#endif
