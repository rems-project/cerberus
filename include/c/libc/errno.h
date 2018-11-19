#ifndef	_ERRNO_H_
#define	_ERRNO_H_

#define EDOM   __cerbvar_EDOM
#define EILSEQ __cerbvar_EILSEQ
#define ERANGE __cerbvar_ERANGE

_Thread_local unsigned int __cerbvar_errno;
#define errno  (*__cerbvar_errno())

void __cerbvar_set_errno(unsigned int n)
{
  errno = n;
}

// Annex K: Bounds-checking interfaces
typedef int errno_t;


#include "../posix/errno.h"

#else
#endif
