#define _Noreturn

#include <limits.h>
#include <stdalign.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define __restrict__
#define __extension__
#define __attribute__(a)

#define __INT32_TYPE__    int
#define __UINT32_TYPE__   unsigned int
#define __INTPTR_TYPE__   int*
#define __UINTPTR_TYPE__  unsigned int*
#define __WCHAR_TYPE__    char
#define __INT_LEAST8_TYPE__ char

#define __inline__        inline
#define __alignof__       alignof
#define __SIZE_TYPE__     __cerbty_size_t

#define __CHAR_BIT__      CHAR_BIT
#define __INT_MAX__       INT_MAX
#define __SCHAR_MAX__     SCHAR_MAX
//#define __LONG_LONG_MAX__ __cerbvar_LLONG_MAX

#define __builtin_abort     abort
#define __builtin_printf    printf
#define __builtin_snprintf  snprintf
#define __builtin_memcpy    memcpy
#define __builtin_memcmp    memcmp
#define __builtin_memset    memset
#define __builtin_strlen    strlen
#define __builtin_strcpy    strcpy
#define __builtin_strcmp    strcmp
#define __builtin_offsetof  offsetof
#define __builtin_abs       abs

// I need to set this explicitly, some tests verify this at preprocessor level
#define __LONG_LONG_MAX__ 9223372036854775807LL
#define __SIZEOF_INT__    4

#define exit(n) return n
#define abort() return 1