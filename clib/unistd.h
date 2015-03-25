#ifndef _UNISTD_H_
#define	_UNISTD_H_

#include <sys/types.h>

ssize_t write(int fildes, const void *buf, size_t nbyte);
ssize_t read(int fildes, void *buf, size_t nbyte);

ssize_t writev(int fildes, const struct iovec *iov, int iovcnt);


int close(int fildes);

#define STDIN_FILENO  0
#define STDOUT_FILENO 1
#define STDERR_FILENO 2

#else
#endif
