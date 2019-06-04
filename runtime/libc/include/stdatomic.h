#ifndef _STDATOMIC_H_
#define _STDATOMIC_H_

#include <stdint.h>
#include <stddef.h>

#define ATOMIC_BOOL_LOCK_FREE      __cerbvar_ATOMIC_BOOL_LOCK_FREE
#define ATOMIC_CHAR_LOCK_FREE      __cerbvar_ATOMIC_CHAR_LOCK_FREE
#define ATOMIC_CHAR16_T_LOCK_FREE  __cerbvar_ATOMIC_CHAR16_LOCK_FREE
#define ATOMIC_CHAR32_T_LOCK_FREE  __cerbvar_ATOMIC_CHAR32_LOCK_FREE
#define ATOMIC_WCHAR_T_LOCK_FREE   __cerbvar_ATOMIC_WCHAR_LOCK_FREE
#define ATOMIC_SHORT_LOCK_FREE     __cerbvar_ATOMIC_SHORT_LOCK_FREE
#define ATOMIC_INT_LOCK_FREE       __cerbvar_ATOMIC_INT_LOCK_FREE
#define ATOMIC_LONG_LOCK_FREE      __cerbvar_ATOMIC_LONG_LOCK_FREE
#define ATOMIC_LLONG_LOCK_FREE     __cerbvar_ATOMIC_LLONG_LOCK_FREE
#define ATOMIC_POINTER_LOCK_FREE   __cerbvar_ATOMIC_POINTER_LOCK_FREE

#define ATOMIC_FLAG_INIT           __cerbvar_ATOMIC_FLAG_INIT

typedef enum memory_order {
  memory_order_relaxed = __cerbvar_memory_order_relaxed,
  memory_order_consume = __cerbvar_memory_order_consume,
  memory_order_acquire = __cerbvar_memory_order_acquire,
  memory_order_release = __cerbvar_memory_order_release,
  memory_order_acq_rel = __cerbvar_memory_order_acq_rel,
  memory_order_seq_cst = __cerbvar_memory_order_seq_cst
} memory_order;

// TODO: atomic_flag
// atomic_flag ===> a structure type representing a lock-free, primitive atomic flag; and several atomic analogs of integer types.


#define ATOMIC_VAR_INIT(value) (value)


#define atomic_init(obj, value)    __cerbvar_atomic_init(obj, value)


void atomic_thread_fence(memory_order order);
void atomic_signal_fence(memory_order order);


#define atomic_is_lock_free(obj)    __cerbvar_atomic_is_lock_free(sizeof(obj))

typedef _Atomic(_Bool)                  atomic_bool;
typedef _Atomic(char)                   atomic_char;
typedef _Atomic(signed char)            atomic_schar;
typedef _Atomic(unsigned char)          atomic_uchar;
typedef _Atomic(short)                  atomic_short;
typedef _Atomic(unsigned short)         atomic_ushort;
typedef _Atomic(int)                    atomic_int;
typedef _Atomic(unsigned int)           atomic_uint;
typedef _Atomic(long)                   atomic_long;
typedef _Atomic(unsigned long)          atomic_ulong;
typedef _Atomic(long long)              atomic_llong;
typedef _Atomic(unsigned long long)     atomic_ullong;
//typedef _Atomic(char16_t)               atomic_char16_t;
//typedef _Atomic(char32_t)               atomic_char32_t;
//typedef _Atomic(wchar_t)                atomic_wchar_t;
typedef _Atomic(int_least8_t)           atomic_int_least8_t;
typedef _Atomic(uint_least8_t)          atomic_uint_least8_t;
typedef _Atomic(int_least16_t)          atomic_int_least16_t;
typedef _Atomic(uint_least16_t)         atomic_uint_least16_t;
typedef _Atomic(int_least32_t)          atomic_int_least32_t;
typedef _Atomic(uint_least32_t)         atomic_uint_least32_t;
typedef _Atomic(int_least64_t)          atomic_int_least64_t;
typedef _Atomic(uint_least64_t)         atomic_uint_least64_t;
typedef _Atomic(int_fast8_t)            atomic_int_fast8_t;
typedef _Atomic(uint_fast8_t)           atomic_uint_fast8_t;
typedef _Atomic(int_fast16_t)           atomic_int_fast16_t;
typedef _Atomic(uint_fast16_t)          atomic_uint_fast16_t;
typedef _Atomic(int_fast32_t)           atomic_int_fast32_t;
typedef _Atomic(uint_fast32_t)          atomic_uint_fast32_t;
typedef _Atomic(int_fast64_t)           atomic_int_fast64_t;
typedef _Atomic(uint_fast64_t)          atomic_uint_fast64_t;
typedef _Atomic(intptr_t)               atomic_intptr_t;
typedef _Atomic(uintptr_t)              atomic_uintptr_t;
typedef _Atomic(size_t)                 atomic_size_t;
typedef _Atomic(ptrdiff_t)              atomic_ptrdiff_t;
typedef _Atomic(intmax_t)               atomic_intmax_t;
typedef _Atomic(uintmax_t)              atomic_uintmax_t;


#define atomic_store_explicit \
  __cerbvar_atomic_store_explicit
#define atomic_load_explicit \
  __cerbvar_atomic_load_explicit
#define atomic_exchange_explicit \
  __cerbvar_atomic_exchange_explicit
#define atomic_compare_exchange_strong_explicit \
  __cerbvar_atomic_compare_exchange_strong_explicit
#define atomic_compare_exchange_weak_explicit \
  __cerbvar_atomic_compare_exchange_weak_explicit

// TODO!
#define atomic_fetch_key_explicit \
  __cerbvar_atomic_fetch_key_explicit


#define atomic_store(object, desired) \
  atomic_store_explicit(object, desired, memory_order_seq_cst)
#define atomic_load(object) \
  atomic_load_explicit(object, memory_order_seq_cst)
#define atomic_exchange(object, desired) \
  atomic_exchange_explicit(object, desired, memory_order_seq_cst)
#define atomic_compare_exchange_strong(object, expected, desired) \
  atomic_compare_exchange_strong(object, expected, desired, \
      memory_order_seq_cst, memory_order_seq_cst)
#define atomic_compare_exchange_weak(object, expected, desired) \
  atomic_compare_exchange_weak(object, expected, desired, \
      memory_order_seq_cst, memory_order_seq_cst)
#define atomic_fetch_key(object, operand) \
  atomic_fetch_key_explicit(object, operand, memory_order_seq_cst)

#endif
