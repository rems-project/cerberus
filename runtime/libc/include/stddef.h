#ifndef _STDDEF_H_
#define _STDDEF_H_

typedef __cerbty_ptrdiff_t   ptrdiff_t;
typedef __cerbty_size_t      size_t;
typedef __cerbty_wchar_t     wchar_t;

#ifdef __CHERI__
typedef __cerbty_ptraddr_t   ptraddr_t;
#endif

#ifdef __CHERI_PURE_CAPABILITY__
typedef void* max_align_t;
#else
#define max_align_t          __cerbty_max_align_t;
#endif

#define NULL                 __cerbvar_NULL

// offsetof() is now builtin in the parser

#endif
