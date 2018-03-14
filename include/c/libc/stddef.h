#ifndef	_STDDEF_H_
#define	_STDDEF_H_

typedef __cerbty_ptrdiff_t   ptrdiff_t;
typedef __cerbty_size_t      size_t;
typedef __cerbty_max_align_t max_align_t;

typedef __cerbty_wchar_t wchar_t;

#define NULL                 __cerbvar_NULL
#define offsetof(type, memb) __cerb_offsetof(type, memb)

// Annex K: Bounds-checking interfaces
// typedef size_t rsize_t;

#else
#endif
