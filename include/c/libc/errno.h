#ifndef	_ERRNO_H_
#define	_ERRNO_H_

#define EDOM   __cerbvar_EDOM
#define EILSEQ __cerbvar_EILSEQ
#define ERANGE __cerbvar_ERANGE
#define errno  __cerbvar_errno


// Annex K: Bounds-checking interfaces
typedef int errno_t;


#include "../posix/errno.h"

#else
#endif
