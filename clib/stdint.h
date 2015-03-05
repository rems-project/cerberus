#ifndef	_STDINT_H_
#define	_STDINT_H_

/* The typedef name intN_t designates a signed integer type with width N, no
   padding bits, and a two’s complement representation. */
typedef __cerbty_int8_t  int8_t;
typedef __cerbty_int16_t int16_t;
typedef __cerbty_int32_t int32_t;
typedef __cerbty_int64_t int64_t;

/* The typedef name uintN_t designates an unsigned integer type with width N and
   no padding bits. */
typedef __cerbty_uint8_t  uint8_t;
typedef __cerbty_uint16_t uint16_t;
typedef __cerbty_uint32_t uint32_t;
typedef __cerbty_uint64_t uint64_t;

/* The typedef name int_leastN_t designates a signed integer type with a width
   of at least N, such that no signed integer type with lesser size has at least
   the specified width. */
typedef __cerbty_int_least8_t  int_least8_t;
typedef __cerbty_int_least16_t int_least16_t;
typedef __cerbty_int_least32_t int_least32_t;
typedef __cerbty_int_least64_t int_least64_t;

/* The typedef name uint_leastN_t designates an unsigned integer type with a
   width of at least N, such that no unsigned integer type with lesser size has
   at least the specified width. */
typedef __cerbty_uint_least8_t  uint_least8_t;
typedef __cerbty_uint_least16_t uint_least16_t;
typedef __cerbty_uint_least32_t uint_least32_t;
typedef __cerbty_uint_least64_t uint_least64_t;

/* The typedef name int_fastN_t designates the fastest signed integer type with
   a width of at least N. */
typedef __cerbty_int_fast8_t  int_fast8_t;
typedef __cerbty_int_fast16_t int_fast16_t;
typedef __cerbty_int_fast32_t int_fast32_t;
typedef __cerbty_int_fast64_t int_fast64_t;

/* The typedef name uint_fastN_t designates the fastest unsigned integer type
   with a width of at least N. */
typedef __cerbty_uint_fast8_t  uint_fast8_t;
typedef __cerbty_uint_fast16_t uint_fast16_t;
typedef __cerbty_uint_fast32_t uint_fast32_t;
typedef __cerbty_uint_fast64_t uint_fast64_t;

/* The following type designates a signed integer type with the property that
   any valid pointer to void can be converted to this type, then converted back
   to pointer to void, and the result will compare equal to the original
   pointer: */
/* TODO: optional */
typedef __cerbty_intptr_t intptr_t;

/* The following type designates an unsigned integer type with the property that
   any valid pointer to void can be converted to this type, then converted back
   to pointer to void, and the result will compare equal to the original
   pointer: */
/* TODO: optional */
typedef __cerbty_uintptr_t uintptr_t;

/* The following type designates a signed integer type capable of representing
   any value of any signed integer type: */
typedef __cerbty_intmax_t intmax_t;

/* The following type designates an unsigned integer type capable of
   representing any value of any unsigned integer type: */
typedef __cerbty_uintmax_t uintmax_t;


// Limits of exact-width integer types
#define INT8_MIN   __cerbvar_INT8_MIN
#define INT16_MIN  __cerbvar_INT16_MIN
#define INT32_MIN  __cerbvar_INT32_MIN
#define INT64_MIN  __cerbvar_INT64_MIN

#define INT8_MAX   __cerbvar_INT8_MAX
#define INT16_MAX  __cerbvar_INT16_MAX
#define INT32_MAX  __cerbvar_INT32_MAX
#define INT64_MAX  __cerbvar_INT64_MAX

#define UINT8_MAX   __cerbvar_UINT8_MAX
#define UINT16_MAX  __cerbvar_UINT16_MAX
#define UINT32_MAX  __cerbvar_UINT32_MAX
#define UINT64_MAX  __cerbvar_UINT64_MAX

// Limits of minimum-width integer types
#define INT_LEAST8_MIN   __cerbvar_INT_LEAST8_MIN
#define INT_LEAST16_MIN  __cerbvar_INT_LEAST16_MIN
#define INT_LEAST32_MIN  __cerbvar_INT_LEAST32_MIN
#define INT_LEAST64_MIN  __cerbvar_INT_LEAST64_MIN

#define INT_LEAST8_MAX   __cerbvar_INT_LEAST8_MAX
#define INT_LEAST16_MAX  __cerbvar_INT_LEAST16_MAX
#define INT_LEAST32_MAX  __cerbvar_INT_LEAST32_MAX
#define INT_LEAST64_MAX  __cerbvar_INT_LEAST64_MAX

#define UINT_LEAST8_MAX   __cerbvar_UINT_LEAST8_MAX
#define UINT_LEAST16_MAX  __cerbvar_UINT_LEAST16_MAX
#define UINT_LEAST32_MAX  __cerbvar_UINT_LEAST32_MAX
#define UINT_LEAST64_MAX  __cerbvar_UINT_LEAST64_MAX

// Limits of fastest minimum-width integer types
#define INT_FAST8_MIN   __cerbvar_INT_FAST8_MIN
#define INT_FAST16_MIN  __cerbvar_INT_FAST16_MIN
#define INT_FAST32_MIN  __cerbvar_INT_FAST32_MIN
#define INT_FAST64_MIN  __cerbvar_INT_FAST64_MIN

#define INT_FAST8_MAX   __cerbvar_INT_FAST8_MAX
#define INT_FAST16_MAX  __cerbvar_INT_FAST16_MAX
#define INT_FAST32_MAX  __cerbvar_INT_FAST32_MAX
#define INT_FAST64_MAX  __cerbvar_INT_FAST64_MAX

#define UINT_FAST8_MAX   __cerbvar_UINT_FAST8_MAX
#define UINT_FAST16_MAX  __cerbvar_UINT_FAST16_MAX
#define UINT_FAST32_MAX  __cerbvar_UINT_FAST32_MAX
#define UINT_FAST64_MAX  __cerbvar_UINT_FAST64_MAX

// Limits of integer types capable of holding object pointers
#define INTPTR_MIN   __cerbvar_INTPTR_MIN
#define INTPTR_MAX   __cerbvar_INTPTR_MAX
#define UINTPTR_MAX  __cerbvar_UINTPTR_MAX

// Limits of greatest-width integer types
#define INTMAX_MIN   __cerbvar_INTMAX_MIN
#define INTMAX_MAX   __cerbvar_INTMAX_MAX
#define UINTMAX_MAX  __cerbvar_UINTMAX_MAX

// Limits of other integer types
#define PTRDIFF_MIN     __cerbvar_PTRDIFF_MIN
#define PTRDIFF_MAX     __cerbvar_PTRDIFF_MAX
#define SIG_ATOMIC_MIN  __cerbvar_SIG_ATOMIC_MIN
#define SIG_ATOMIC_MAX  __cerbvar_SIG_ATOMIC_MAX
#define SIZE_MAX        __cerbvar_SIZE_MAX
#define WCHAR_MIN       __cerbvar_WCHAR_MIN
#define WCHAR_MAX       __cerbvar_WCHAR_MAX
#define WINT_MIN        __cerbvar_WINT_MIN
#define WINT_MAX        __cerbvar_WINT_MAX


// TODO
/* #define INTN_C(value)            */
/* #define UINTN_C(value)           */
/* #define INTMAX_C(value)          */
/* #define UINTMAX_C(value)         */
/* #define __STDC_WANT_LIB_EXT1__   */

// TODO RSIZE_MAX

#else
#endif
