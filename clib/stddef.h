#ifndef	_STDDEF_H_
#define	_STDDEF_H_

// typedef __cerb_ptrdiff_t   ptrdiff_t;
// typedef __cerb_size_t      size_t;
// typedef __cerb_max_align_t max_align_t;

#ifndef _STDLIB_H_ // TODO: fix the f!cking parser
typedef __cerbty_wchar_t wchar_t;
#endif

#define NULL                 __cerbvar_NULL
// TODO: #define offsetof(type, memb) __cerb_offsetof(type, memb)

// Annex K: Bounds-checking interfaces
// typedef size_t rsize_t;

#else
#endif
