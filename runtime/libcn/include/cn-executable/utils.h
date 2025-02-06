#ifndef CN_UTILS
#define CN_UTILS 

#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>
// #include <math.h>
// #include <assert.h>
// #include "stdint.h"
#include <stdint.h>

#include <cn-executable/alloc.h>
#include <cn-executable/hash_table.h>

#ifdef __cplusplus
extern "C" {
#endif

enum cn_logging_level {
    CN_LOGGING_NONE = 0,
    CN_LOGGING_ERROR = 1,
    CN_LOGGING_INFO = 2
};

enum cn_logging_level get_cn_logging_level(void);

/** Sets the logging level, returning the previous one */
enum cn_logging_level set_cn_logging_level(enum cn_logging_level new_level);

#define cn_printf(level, ...)\
    if (get_cn_logging_level() >= level) {\
        printf(__VA_ARGS__);\
    }

void cn_print_nr_owned_predicates(void);

struct cn_error_message_info {
    const char *function_name;
    char *file_name;
    int line_number;
    char *cn_source_loc;
    struct cn_error_message_info *parent;
};

void initialise_error_msg_info_(const char *function_name, char *file_name, int line_number);

#define initialise_error_msg_info() initialise_error_msg_info_(__func__, __FILE__, __LINE__)

void reset_error_msg_info();

/* TODO: Implement */
/*struct cn_error_messages {
    struct cn_error_message_info *top_level_error_msg_info;
    struct cn_error_message_info *nested_error_msg_info;
};*/

void update_error_message_info_(const char *function_name, char *file_name, int line_number, char *cn_source_loc);

void cn_pop_msg_info();

#define update_cn_error_message_info(x)\
    update_error_message_info_(__func__, __FILE__, __LINE__ + 1, x)

#define update_cn_error_message_info_access_check(x)\
    update_error_message_info_(__func__, __FILE__, __LINE__, x)

/* Wrappers for C types */

/* Signed bitvectors */

typedef struct cn_bits_i8 {
    int8_t val;
} cn_bits_i8;

typedef struct cn_bits_i16 {
    int16_t val;
} cn_bits_i16;

typedef struct cn_bits_i32 {
    int32_t val;
} cn_bits_i32;

typedef struct cn_bits_i64 {
    int64_t val;
} cn_bits_i64;

/* Unsigned bitvectors */

typedef struct cn_bits_u8 {
    uint8_t val;
} cn_bits_u8;

typedef struct cn_bits_u16 {
    uint16_t val;
} cn_bits_u16;

typedef struct cn_bits_u32 {
    uint32_t val;
} cn_bits_u32;

typedef struct cn_bits_u64 {
    uint64_t val;
} cn_bits_u64;


typedef struct cn_integer {
    signed long val;
} cn_integer;

typedef struct cn_pointer {
    void *ptr;
} cn_pointer;

typedef struct cn_bool {
    _Bool val;
} cn_bool;

typedef struct cn_alloc_id {
    uint8_t val;
} cn_alloc_id;


typedef hash_table cn_map;

void initialise_ownership_ghost_state(void);
void initialise_ghost_stack_depth(void);
signed long get_cn_stack_depth(void);
void ghost_stack_depth_incr(void);
void ghost_stack_depth_decr(void);


/* malloc, free */
void *cn_aligned_alloc(size_t align, size_t size) ;
void *cn_malloc(unsigned long size) ;
void *cn_calloc(size_t num, size_t size) ;
void cn_free_sized(void*, size_t len);

void cn_print_nr_u64(int i, unsigned long u) ;
void cn_print_u64(const char *str, unsigned long u) ;

/* cn_failure callbacks */
enum cn_failure_mode {
    CN_FAILURE_ASSERT = 1,
    CN_FAILURE_CHECK_OWNERSHIP,
    CN_FAILURE_OWNERSHIP_LEAK,
    CN_FAILURE_ALLOC
};

typedef void (*cn_failure_callback)(enum cn_failure_mode);
void set_cn_failure_cb(cn_failure_callback callback);
void reset_cn_failure_cb(void);
void cn_failure(enum cn_failure_mode mode);

/* Conversion functions */

cn_bool *convert_to_cn_bool(_Bool b);
_Bool convert_from_cn_bool(cn_bool *b);
void cn_assert(cn_bool *cn_b);
cn_bool *cn_bool_and(cn_bool *b1, cn_bool *b2);
cn_bool *cn_bool_or(cn_bool *b1, cn_bool *b2);
cn_bool *cn_bool_not(cn_bool *b);
cn_bool *cn_bool_implies(cn_bool *b1, cn_bool *b2);
cn_bool *cn_bool_equality(cn_bool *b1, cn_bool *b2);
void *cn_ite(cn_bool *b, void *e1, void *e2);

cn_map *map_create(void);
cn_map *cn_map_set(cn_map *m, cn_integer *key, void *value);
cn_map *cn_map_deep_copy(cn_map *m1);
cn_bool *cn_map_equality(cn_map *m1, cn_map *m2, cn_bool *(value_equality_fun)(void *, void *));
// TODO (RB) does this need to be in here, or should it be auto-generated?
// See https://github.com/rems-project/cerberus/pull/652 for details
cn_bool *void_pointer_equality(void *p1, void *p2);

#define convert_to_cn_map(c_ptr, cntype_conversion_fn, num_elements)({\
    cn_map *m = map_create();\
    for (int i = 0; i < num_elements; i++) {\
        cn_map_set(m, convert_to_cn_integer(i), cntype_conversion_fn(c_ptr[i]));\
    }\
    m;\
})
#define convert_from_cn_map(arr, m, cntype, num_elements)\
    for (int i = 0; i < num_elements; i++) {\
        arr[i] = convert_from_##cntype(cn_map_get_##cntype(m, convert_to_cn_integer(i)));\
    }


cn_bool *cn_pointer_equality(void *i1, void *i2);
cn_bool *cn_pointer_is_null(cn_pointer *);
cn_bool *cn_pointer_le(cn_pointer *i1, cn_pointer *i2);
cn_bool *cn_pointer_lt(cn_pointer *i1, cn_pointer *i2);
cn_bool *cn_pointer_ge(cn_pointer *i1, cn_pointer *i2);
cn_bool *cn_pointer_gt(cn_pointer *i1, cn_pointer *i2);


#define cn_pointer_deref(CN_PTR, CTYPE)\
    *((CTYPE *) CN_PTR->ptr)

/* CN integer type auxilliary functions */


#define CN_GEN_EQUALITY(CNTYPE)\
    CN_GEN_EQUALITY_(CNTYPE)

#define CN_GEN_EQUALITY_(CNTYPE)\
    static inline cn_bool *CNTYPE##_equality(void *i1, void *i2){\
        return convert_to_cn_bool(((CNTYPE *) i1)->val == ((CNTYPE *) i2)->val);\
    }

#define CN_GEN_CONVERT(CTYPE, CNTYPE)\
    static inline CNTYPE *convert_to_##CNTYPE(CTYPE i) {\
        CNTYPE *ret = (CNTYPE *) cn_bump_malloc(sizeof(CNTYPE));\
        ret->val = i;\
        return ret;\
    }

#define CN_GEN_CONVERT_FROM(CTYPE, CNTYPE)\
    static inline CTYPE convert_from_##CNTYPE(CNTYPE *i) {\
        return i->val;\
    }

/* Arithmetic operators */

#define CN_GEN_LT(CNTYPE)\
    static inline cn_bool *CNTYPE##_lt(CNTYPE *i1, CNTYPE *i2) {\
        return convert_to_cn_bool(i1->val < i2->val);\
    }

#define CN_GEN_LE(CNTYPE)\
    static inline cn_bool *CNTYPE##_le(CNTYPE *i1, CNTYPE *i2) {\
        return convert_to_cn_bool(i1->val <= i2->val);\
    }

#define CN_GEN_GT(CNTYPE)\
    static inline cn_bool *CNTYPE##_gt(CNTYPE *i1, CNTYPE *i2) {\
        return convert_to_cn_bool(i1->val > i2->val);\
    }

#define CN_GEN_GE(CNTYPE)\
    static inline cn_bool *CNTYPE##_ge(CNTYPE *i1, CNTYPE *i2) {\
        return convert_to_cn_bool(i1->val >= i2->val);\
    }

#define CN_GEN_NEGATE(CNTYPE)\
    static inline CNTYPE *CNTYPE##_negate(CNTYPE *i) {\
        return convert_to_##CNTYPE(-(i->val));\
    }


#define CN_GEN_ADD(CTYPE, CNTYPE)\
    static inline CNTYPE *CNTYPE##_add(CNTYPE *i1, CNTYPE *i2) {\
        CNTYPE *res = (CNTYPE *) cn_bump_malloc(sizeof(CNTYPE));\
        res->val = i1->val + i2->val;\
        return res;\
    }

#define CN_GEN_SUB(CTYPE, CNTYPE)\
    static inline CNTYPE *CNTYPE##_sub(CNTYPE *i1, CNTYPE *i2) {\
        CNTYPE *res = (CNTYPE *) cn_bump_malloc(sizeof(CNTYPE));\
        res->val = i1->val - i2->val;\
        return res;\
    }

#define CN_GEN_MUL(CTYPE, CNTYPE)\
    static inline CNTYPE *CNTYPE##_multiply(CNTYPE *i1, CNTYPE *i2) {\
        CNTYPE *res = (CNTYPE *) cn_bump_malloc(sizeof(CNTYPE));\
        res->val = i1->val * i2->val;\
        return res;\
    }

#define CN_GEN_DIV(CTYPE, CNTYPE)\
    static inline CNTYPE *CNTYPE##_divide(CNTYPE *i1, CNTYPE *i2) {\
        CNTYPE *res = (CNTYPE *) cn_bump_malloc(sizeof(CNTYPE));\
        res->val = i1->val / i2->val;\
        return res;\
    }

#define CN_GEN_SHIFT_LEFT(CTYPE, CNTYPE)\
    static inline CNTYPE *CNTYPE##_shift_left(CNTYPE *i1, CNTYPE *i2) {\
        CNTYPE *res = (CNTYPE *) cn_bump_malloc(sizeof(CNTYPE));\
        res->val = i1->val << i2->val;\
        return res;\
    }

#define CN_GEN_SHIFT_RIGHT(CTYPE, CNTYPE)\
    static inline CNTYPE *CNTYPE##_shift_right(CNTYPE *i1, CNTYPE *i2) {\
        CNTYPE *res = (CNTYPE *) cn_bump_malloc(sizeof(CNTYPE));\
        res->val = i1->val >> i2->val;\
        return res;\
    }

#define CN_GEN_MIN(CNTYPE)\
    static inline CNTYPE *CNTYPE##_min(CNTYPE *i1, CNTYPE *i2) {\
        return convert_from_cn_bool(CNTYPE##_lt(i1, i2)) ? i1 : i2;\
    }

#define CN_GEN_MAX(CNTYPE)\
    static inline CNTYPE *CNTYPE##_max(CNTYPE *i1, CNTYPE *i2) {\
        return convert_from_cn_bool(CNTYPE##_gt(i1, i2)) ? i1 : i2;\
    }

/* TODO: Account for UB: https://stackoverflow.com/a/20638659 */
#define CN_GEN_MOD(CTYPE, CNTYPE)\
    static inline CNTYPE *CNTYPE##_mod(CNTYPE *i1, CNTYPE *i2) {\
        CNTYPE *res = (CNTYPE *) cn_bump_malloc(sizeof(CNTYPE));\
        res->val = i1->val % i2->val;\
        if (res->val < 0) {\
            res->val = (i2->val < 0) ? res->val - i2->val : res->val + i2->val;\
        }\
        return res;\
    }


#define CN_GEN_REM(CTYPE, CNTYPE)\
    static inline CNTYPE *CNTYPE##_rem(CNTYPE *i1, CNTYPE *i2) {\
        CNTYPE *res = (CNTYPE *) cn_bump_malloc(sizeof(CNTYPE));\
        res->val = i1->val % i2->val;\
        return res;\
    }

#define CN_GEN_XOR(CTYPE, CNTYPE)\
    static inline CNTYPE *CNTYPE##_xor(CNTYPE *i1, CNTYPE *i2) {\
        CNTYPE *res = (CNTYPE *) cn_bump_malloc(sizeof(CNTYPE));\
        res->val = i1->val ^ i2->val;\
        return res;\
    }

#define CN_GEN_BWAND(CTYPE, CNTYPE)\
    static inline CNTYPE *CNTYPE##_bwand(CNTYPE *i1, CNTYPE *i2) {\
        CNTYPE *res = (CNTYPE *) cn_bump_malloc(sizeof(CNTYPE));\
        res->val = i1->val & i2->val;\
        return res;\
    }

#define CN_GEN_BWOR(CTYPE, CNTYPE)\
    static inline CNTYPE *CNTYPE##_bwor(CNTYPE *i1, CNTYPE *i2) {\
        CNTYPE *res = (CNTYPE *) cn_bump_malloc(sizeof(CNTYPE));\
        res->val = i1->val | i2->val;\
        return res;\
    }

cn_bits_u32 *cn_bits_u32_fls(cn_bits_u32 *i1);
cn_bits_u64 *cn_bits_u64_flsl(cn_bits_u64 *i1);

static inline int ipow(int base, int exp)
{
    int result = 1;
    for (;;)
    {
        if (exp & 1)
            result *= base;
        exp >>= 1;
        if (!exp)
            break;
        base *= base;
    }

    return result;
}

#define CN_GEN_POW(CTYPE, CNTYPE)\
    static inline CNTYPE *CNTYPE##_pow(CNTYPE *i1, CNTYPE *i2) {\
        CNTYPE *res = (CNTYPE *) cn_bump_malloc(sizeof(CNTYPE));\
        res->val = ipow(i1->val, i2->val);\
        return res;\
    }


#define cn_array_shift(cn_ptr, size, index)\
    convert_to_cn_pointer((char *) cn_ptr->ptr + (index->val * size)) 


#define cn_member_shift(cn_ptr, tag, member_name)\
  convert_to_cn_pointer(&(((struct tag *) cn_ptr->ptr)->member_name))



#define CN_GEN_INCREMENT(CNTYPE)\
    static inline CNTYPE *CNTYPE##_increment(CNTYPE *i) {\
        i->val = i->val + 1;\
        return i;\
    }

#define CN_GEN_PTR_ADD(CNTYPE)\
    static inline cn_pointer *cn_pointer_add_##CNTYPE(cn_pointer *ptr, CNTYPE *i) {\
        cn_pointer *res = (cn_pointer *) cn_bump_malloc(sizeof(cn_pointer));\
        res->ptr = (char *) ptr->ptr + i->val;\
        return res;\
    }


/* Casting functions */

#define CN_GEN_CAST_TO_PTR(CNTYPE, INTPTR_TYPE)\
    static inline cn_pointer *cast_##CNTYPE##_to_cn_pointer(CNTYPE *i) {\
        cn_pointer *res = (cn_pointer *) cn_bump_malloc(sizeof(cn_pointer));\
        res->ptr = (void *) (INTPTR_TYPE) i->val;\
        return res;\
    }

#define CN_GEN_CAST_FROM_PTR(CTYPE, CNTYPE, INTPTR_TYPE)\
    static inline CNTYPE *cast_cn_pointer_to_##CNTYPE(cn_pointer *ptr) {\
        CNTYPE *res = (CNTYPE *) cn_bump_malloc(sizeof(CNTYPE));\
        res->val = (CTYPE) (INTPTR_TYPE) (ptr->ptr);\
        return res;\
    }


#define CN_GEN_CAST_INT_TYPES(CNTYPE1, CTYPE2, CNTYPE2)\
    static inline CNTYPE2 *cast_##CNTYPE1##_to_##CNTYPE2(CNTYPE1 *i) {\
        CNTYPE2 *res = (CNTYPE2 *) cn_bump_malloc(sizeof(CNTYPE2));\
        res->val = (CTYPE2) i->val;\
        return res;\
    }

#define CN_GEN_DEFAULT(CNTYPE)                      \
    static inline CNTYPE *default_##CNTYPE(void) {  \
        return convert_to_##CNTYPE(0);              \
    }

cn_map *default_cn_map(void);
cn_bool *default_cn_bool(void);

#define CN_GEN_MAP_GET(CNTYPE)\
    static inline void *cn_map_get_##CNTYPE(cn_map *m, cn_integer *key) {   \
        signed long *key_ptr = cn_bump_malloc(sizeof(signed long));         \
        *key_ptr = key->val;                                                \
        void *res = ht_get(m, key_ptr);                                     \
        if (!res) { return (void *) default_##CNTYPE(); }                   \
        return res;                                                         \
    }


#define CN_GEN_CASTS_INNER(CTYPE, CNTYPE)               \
    CN_GEN_CAST_INT_TYPES(cn_bits_i8, CTYPE, CNTYPE)    \
    CN_GEN_CAST_INT_TYPES(cn_bits_i16, CTYPE, CNTYPE)   \
    CN_GEN_CAST_INT_TYPES(cn_bits_i32, CTYPE, CNTYPE)   \
    CN_GEN_CAST_INT_TYPES(cn_bits_i64, CTYPE, CNTYPE)   \
    CN_GEN_CAST_INT_TYPES(cn_bits_u8, CTYPE, CNTYPE)    \
    CN_GEN_CAST_INT_TYPES(cn_bits_u16, CTYPE, CNTYPE)   \
    CN_GEN_CAST_INT_TYPES(cn_bits_u32, CTYPE, CNTYPE)   \
    CN_GEN_CAST_INT_TYPES(cn_bits_u64, CTYPE, CNTYPE)   \
    CN_GEN_CAST_INT_TYPES(cn_integer, CTYPE, CNTYPE)    \


#define CN_GEN_PTR_CASTS_UNSIGNED(CTYPE, CNTYPE)    \
    CN_GEN_CAST_TO_PTR(CNTYPE, uintptr_t)           \
    CN_GEN_CAST_FROM_PTR(CTYPE, CNTYPE, uintptr_t)  \

#define CN_GEN_PTR_CASTS_SIGNED(CTYPE, CNTYPE)      \
    CN_GEN_CAST_TO_PTR(CNTYPE, intptr_t)            \
    CN_GEN_CAST_FROM_PTR(CTYPE, CNTYPE, intptr_t)   \


#define CN_GEN_ALL(CTYPE, CNTYPE)\
    CN_GEN_ALL_(CTYPE, CNTYPE)

#define CN_GEN_ALL_(CTYPE, CNTYPE)      \
   CN_GEN_CONVERT(CTYPE, CNTYPE)        \
   CN_GEN_CONVERT_FROM(CTYPE, CNTYPE)   \
   CN_GEN_EQUALITY(CNTYPE)              \
   CN_GEN_LT(CNTYPE)                    \
   CN_GEN_LE(CNTYPE)                    \
   CN_GEN_GT(CNTYPE)                    \
   CN_GEN_GE(CNTYPE)                    \
   CN_GEN_NEGATE(CNTYPE)                \
   CN_GEN_ADD(CTYPE, CNTYPE)            \
   CN_GEN_SUB(CTYPE, CNTYPE)            \
   CN_GEN_MUL(CTYPE, CNTYPE)            \
   CN_GEN_DIV(CTYPE, CNTYPE)            \
   CN_GEN_SHIFT_LEFT(CTYPE, CNTYPE)     \
   CN_GEN_SHIFT_RIGHT(CTYPE, CNTYPE)    \
   CN_GEN_MIN(CNTYPE)                   \
   CN_GEN_MAX(CNTYPE)                   \
   CN_GEN_MOD(CTYPE, CNTYPE)            \
   CN_GEN_REM(CTYPE, CNTYPE)            \
   CN_GEN_XOR(CTYPE, CNTYPE)            \
   CN_GEN_BWAND(CTYPE, CNTYPE)          \
   CN_GEN_BWOR(CTYPE, CNTYPE)           \
   CN_GEN_POW(CTYPE, CNTYPE)            \
   CN_GEN_INCREMENT(CNTYPE)             \
   CN_GEN_PTR_ADD(CNTYPE)               \
   CN_GEN_CASTS_INNER(CTYPE, CNTYPE)    \
   CN_GEN_DEFAULT(CNTYPE)               \
   CN_GEN_MAP_GET(CNTYPE)               \


CN_GEN_ALL(int8_t, cn_bits_i8)
CN_GEN_ALL(int16_t, cn_bits_i16)
CN_GEN_ALL(int32_t, cn_bits_i32)
CN_GEN_ALL(int64_t, cn_bits_i64)
CN_GEN_ALL(uint8_t, cn_bits_u8)
CN_GEN_ALL(uint16_t, cn_bits_u16)
CN_GEN_ALL(uint32_t, cn_bits_u32)
CN_GEN_ALL(uint64_t, cn_bits_u64)
CN_GEN_ALL(signed long, cn_integer)


CN_GEN_PTR_CASTS_SIGNED(int8_t, cn_bits_i8)
CN_GEN_PTR_CASTS_SIGNED(int16_t, cn_bits_i16)
CN_GEN_PTR_CASTS_SIGNED(int32_t, cn_bits_i32)
CN_GEN_PTR_CASTS_SIGNED(int64_t, cn_bits_i64)
CN_GEN_PTR_CASTS_UNSIGNED(uint8_t, cn_bits_u8)
CN_GEN_PTR_CASTS_UNSIGNED(uint16_t, cn_bits_u16)
CN_GEN_PTR_CASTS_UNSIGNED(uint32_t, cn_bits_u32)
CN_GEN_PTR_CASTS_UNSIGNED(uint64_t, cn_bits_u64)
CN_GEN_PTR_CASTS_SIGNED(signed long, cn_integer)


cn_pointer *convert_to_cn_pointer(void *ptr);
void *convert_from_cn_pointer(cn_pointer *cn_ptr);
cn_pointer *cn_pointer_add(cn_pointer *ptr, cn_integer *i);
cn_pointer *cast_cn_pointer_to_cn_pointer(cn_pointer *p);

CN_GEN_CONVERT(uint8_t, cn_alloc_id)
CN_GEN_EQUALITY(cn_alloc_id)
CN_GEN_DEFAULT(cn_pointer)               
CN_GEN_MAP_GET(cn_pointer)              
CN_GEN_MAP_GET(cn_map)              


/* OWNERSHIP */

enum OWNERSHIP {
    GET,
    PUT
};

int ownership_ghost_state_get(signed long *address_key);
void ownership_ghost_state_set(signed long* address_key, int stack_depth_val);
void ownership_ghost_state_remove(signed long* address_key);

/* CN ownership checking */
void cn_get_ownership(uintptr_t generic_c_ptr, size_t size);
void cn_put_ownership(uintptr_t generic_c_ptr, size_t size);
void cn_assume_ownership(void *generic_c_ptr, unsigned long size, char *fun);
void cn_get_or_put_ownership(enum OWNERSHIP owned_enum, uintptr_t generic_c_ptr, size_t size);

/* C ownership checking */
void c_add_to_ghost_state(uintptr_t ptr_to_local, size_t size, signed long stack_depth);
void c_remove_from_ghost_state(uintptr_t ptr_to_local, size_t size);
void c_ownership_check(char *access_kind, uintptr_t generic_c_ptr, int offset, signed long expected_stack_depth);

// Unused 
#define c_concat_with_mapping_stat(STAT, CTYPE, VAR_NAME, GHOST_STATE, STACK_DEPTH)\
    STAT; c_add_to_ghost_state((uintptr_t) &VAR_NAME, GHOST_STATE, sizeof(CTYPE), STACK_DEPTH);

#define c_declare_and_map_local(CTYPE, VAR_NAME)\
    c_concat_with_mapping_stat(CTYPE VAR_NAME, CTYPE, VAR_NAME)

#define c_declare_init_and_map_local(CTYPE, VAR_NAME, EXPR)\
    c_concat_with_mapping_stat(CTYPE VAR_NAME = EXPR, CTYPE, VAR_NAME)
// /Unused


static inline void cn_load(void *ptr, size_t size)
{
//   cn_printf(CN_LOGGING_INFO, "  \x1b[31mLOAD\x1b[0m[%lu] - ptr: %p\n", size, ptr);
}
static inline void cn_store(void *ptr, size_t size)
{
//   cn_printf(CN_LOGGING_INFO, "  \x1b[31mSTORE\x1b[0m[%lu] - ptr: %p\n", size, ptr);
}
static inline void cn_postfix(void *ptr, size_t size)
{
//   cn_printf(CN_LOGGING_INFO, "  \x1b[31mPOSTFIX\x1b[0m[%lu] - ptr: %p\n", size, ptr);
}

// use this macro to wrap an argument to another macro that contains commas 
#define CN_IGNORE_COMMA(...) __VA_ARGS__

#define CN_LOAD(LV)                                           \
  ({                                                          \
    typeof(LV) *__tmp = &(LV);                                \
    update_cn_error_message_info_access_check(NULL);          \
    c_ownership_check("Load", (uintptr_t) __tmp, sizeof(typeof(LV)), get_cn_stack_depth()); \
    cn_load(__tmp, sizeof(typeof(LV)));                       \
    *__tmp;                                                   \
  })

#define CN_STORE_OP(LV, op, X)                                \
 ({                                                           \
    typeof(LV) *__tmp;                                        \
    __tmp = &(LV);                                            \
    update_cn_error_message_info_access_check(NULL);          \
    c_ownership_check("Store", (uintptr_t) __tmp, sizeof(typeof(LV)), get_cn_stack_depth()); \
    cn_store(__tmp, sizeof(typeof(LV)));                      \
    *__tmp op##= (X);                                         \
 })

#define CN_STORE(LV, X) CN_STORE_OP(LV,,X)

#define CN_POSTFIX(LV, OP)                                    \
 ({                                                           \
    typeof(LV) *__tmp;                                        \
    __tmp = &(LV);                                            \
    update_cn_error_message_info_access_check(NULL);          \
    c_ownership_check("Postfix operation", (uintptr_t) __tmp, sizeof(typeof(LV)), get_cn_stack_depth()); \
    cn_postfix(__tmp, sizeof(typeof(LV)));                    \
    (*__tmp) OP;                                              \
 })

#ifdef __cplusplus
}
#endif

#endif // CN_UTILS
