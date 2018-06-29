#include <limits.h>
#include <stdalign.h>
#include <stdint.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdbool.h>
#include <math.h>
#include <float.h>

#ifdef __cerb__

#define float double

#define __const           const
#define __restrict
#define __restrict__
#define __extension__
#define __attribute(a)
#define __attribute__(a)
#define __inline          inline
#define __inline__        inline
#define __alignof__       alignof

#define __SIZE_TYPE__         size_t
#define __PTRDIFF_TYPE__      ptrdiff_t
#define __WCHAR_TYPE__        wchar_t
#define __WINT_TYPE__         wint_t
#define __INTMAX_TYPE__       intmax_t
#define __UINTMAX_TYPE__      uintmax_t
#define __SIG_ATOMIC_TYPE__   sig_atomic_t
#define __INT8_TYPE__         int8_t
#define __INT16_TYPE__        int16_t
#define __INT32_TYPE__        int32_t
#define __INT64_TYPE__        int64_t
#define __UINT8_TYPE__        uint8_t
#define __UINT16_TYPE__       uint16_t
#define __UINT32_TYPE__       uint32_t
#define __UINT64_TYPE__       uint64_t
#define __INT_LEAST8_TYPE__   int_least8_t
#define __INT_LEAST16_TYPE__  int_least16_t
#define __INT_LEAST32_TYPE__  int_least32_t
#define __INT_LEAST64_TYPE__  int_least64_t
#define __UINT_LEAST8_TYPE__  uint_least8_t
#define __UINT_LEAST16_TYPE__ uint_least16_t
#define __UINT_LEAST32_TYPE__ uint_least32_t
#define __UINT_LEAST64_TYPE__ uint_least64_t
#define __INT_FAST8_TYPE__    int_fast8_t
#define __INT_FAST16_TYPE__   int_fast16_t
#define __INT_FAST32_TYPE__   int_fast32_t
#define __INT_FAST64_TYPE__   int_fast64_t
#define __UINT_FAST8_TYPE__   uint_fast8_t
#define __UINT_FAST16_TYPE__  uint_fast16_t
#define __UINT_FAST32_TYPE__  uint_fast32_t
#define __UINT_FAST64_TYPE__  uint_fast64_t
#define __INTPTR_TYPE__       intptr_t
#define __UINTPTR_TYPE__      uintptr_t

// Hard-coded sizes
#define __SIZEOF_LONG_LONG__  8
#define __LONG_LONG_MAX__     LLONG_MAX
#define __SIZEOF_INT__        4
#undef CHAR_BIT
#define CHAR_BIT              8
#define __CHAR_BIT__          CHAR_BIT
#define __LONG_MAX__          2147483647
#define __FLT_MAX__           3.402823e+38
#define __FLT_MIN__           1.175494e-38
#define __INT_MAX__           INT_MAX
#define __SCHAR_MAX__         SCHAR_MAX
#define __DBL_MANT_DIG__      1

#define __builtin_isinff    isinf
#define __builtin_isinf     isinf
#define __builtin_isinfl    isinf
#define __builtin_alloca    alloca
#define __builtin_malloc    malloc
#define __builtin_offset    offsetof
#define __builtin_abort     abort
#define __builtin_printf    printf
#define __builtin_sprintf   sprintf
#define __builtin_snprintf  snprintf
#define __builtin_memcpy    memcpy
#define __builtin_memcmp    memcmp
#define __builtin_memset    memset
#define __builtin_strlen    strlen
#define __builtin_strcpy    strcpy
#define __builtin_strcmp    strcmp
#define __builtin_offsetof  offsetof
#define __builtin_abs       abs

#define __BEGIN_DECLS
#define __END_DECLS

#define __ORDER_LITTLE_ENDIAN__   1
#define __BYTE_ORDER__            __ORDER_LITTLE_ENDIAN__

// Hack implementation of fabs
float fabs(float x)
{
  return (float)(int)x;
}

#endif
