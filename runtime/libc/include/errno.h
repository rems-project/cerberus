#ifndef _ERRNO_H_
#define _ERRNO_H_

// Annex K: Bounds-checking interfaces
typedef int errno_t;

// Expands to integer constant expressions with type int
#define EDOM    __cerbvar_EDOM
#define EILSEQ  __cerbvar_EILSEQ
#define ERANGE  __cerbvar_ERANGE

// Expands to a modifiable lvalue that has type int and thread local
// storage duration
errno_t* __builtin_errno (void);
#define errno (*__builtin_errno())


// Additional macro definitions, beginning with E and a digit or E and an
// uppercase letter,
#include "posix/errno.h"

#endif
