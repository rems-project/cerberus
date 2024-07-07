#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>
// #include <math.h>
// #include <assert.h>
// #include "stdint.h"
#include <stdint.h>

#include <cn-executable/alloc.h>
#include <cn-executable/hash_table.h>

struct cn_error_message_info {
    const char *function_name;
    char *file_name;
    int line_number;
    char *cn_source_loc;
};

/* TODO: Implement */
struct cn_error_messages {
    struct cn_error_message_info *top_level_error_msg_info;
    struct cn_error_message_info *nested_error_msg_info;
};

void update_error_message_info_(struct cn_error_message_info *error_msg_info, const char *function_name, char *file_name, int line_number, char *cn_source_loc);

#define update_cn_error_message_info(x, y)\
    update_error_message_info_(x, __func__, __FILE__, __LINE__ + 1, y)

/* Wrappers for C types */

/* Signed bitvectors */

typedef struct cn_bits_i8 {
    signed char *val;
} cn_bits_i8;

typedef struct cn_bits_i16 {
    signed short *val;
} cn_bits_i16;

typedef struct cn_bits_i32 {
    signed long *val;
} cn_bits_i32;

typedef struct cn_bits_i64 {
    signed long long *val;
} cn_bits_i64;

/* Unsigned bitvectors */

typedef struct cn_bits_u8 {
    unsigned char *val;
} cn_bits_u8;

typedef struct cn_bits_u16 {
    unsigned short *val;
} cn_bits_u16;

typedef struct cn_bits_u32 {
    unsigned long *val;
} cn_bits_u32;

typedef struct cn_bits_u64 {
    unsigned long long *val;
} cn_bits_u64;


typedef struct cn_integer {
    signed long *val;
} cn_integer;

typedef struct cn_pointer {
    void *ptr;
} cn_pointer;

typedef struct cn_bool {
    _Bool val;
} cn_bool;


typedef hash_table cn_map;
typedef hash_table ownership_ghost_state;

ownership_ghost_state *initialise_ownership_ghost_state(void);

/* Conversion functions */

cn_bool *convert_to_cn_bool(_Bool b);
_Bool convert_from_cn_bool(cn_bool *b);
void cn_assert(cn_bool *cn_b, struct cn_error_message_info *error_msg_info);
cn_bool *cn_bool_and(cn_bool *b1, cn_bool *b2);
cn_bool *cn_bool_or(cn_bool *b1, cn_bool *b2);
cn_bool *cn_bool_not(cn_bool *b);
cn_bool *cn_bool_equality(cn_bool *b1, cn_bool *b2);
void *cn_ite(cn_bool *b, void *e1, void *e2);

cn_map *map_create(void);
void *cn_map_get(cn_map *m, cn_integer *key);
void cn_map_set(cn_map *m, cn_integer *key, void *value);
cn_bool *cn_map_equality(cn_map *m1, cn_map *m2, cn_bool *(value_equality_fun)(void *, void *));

#define convert_to_cn_map(c_ptr, cntype_conversion_fn, num_elements)({\
    cn_map *m = map_create();\
    for (int i = 0; i < num_elements; i++) {\
        cn_map_set(m, convert_to_cn_integer(i), cntype_conversion_fn(c_ptr[i]));\
    }\
    m;\
})

cn_bool *cn_pointer_equality(void *i1, void *i2);
cn_bool *cn_pointer_is_null(cn_pointer *);

/* CN integer type auxilliary functions */

#define CN_GEN_EQUALITY(CNTYPE)\
    CN_GEN_EQUALITY_(CNTYPE)

#define CN_GEN_EQUALITY_(CNTYPE)\
    static inline cn_bool *CNTYPE##_equality(void *i1, void *i2){\
        return convert_to_cn_bool((*((CNTYPE *) i1)->val) == (*((CNTYPE *) i2)->val));\
    }

#define CN_GEN_CONVERT(CTYPE, CNTYPE)\
    static inline CNTYPE *convert_to_##CNTYPE(CTYPE i) {\
        CNTYPE *ret = (CNTYPE *) alloc(sizeof(CNTYPE));\
        ret->val = (CTYPE *) alloc(sizeof(CTYPE));\
        *(ret->val) = i;\
        return ret;\
    }

#define CN_GEN_CONVERT_FROM(CTYPE, CNTYPE)\
    static inline CTYPE convert_from_##CNTYPE(CNTYPE *i) {\
        return *i->val;\
    }

/* Arithmetic operators */

#define CN_GEN_LT(CNTYPE)\
    static inline cn_bool *CNTYPE##_lt(CNTYPE *i1, CNTYPE *i2) {\
        return convert_to_cn_bool(*(i1->val) < *(i2->val));\
    }

#define CN_GEN_LE(CNTYPE)\
    static inline cn_bool *CNTYPE##_le(CNTYPE *i1, CNTYPE *i2) {\
        return convert_to_cn_bool(*(i1->val) <= *(i2->val));\
    }

#define CN_GEN_GT(CNTYPE)\
    static inline cn_bool *CNTYPE##_gt(CNTYPE *i1, CNTYPE *i2) {\
        return convert_to_cn_bool(*(i1->val) > *(i2->val));\
    }

#define CN_GEN_GE(CNTYPE)\
    static inline cn_bool *CNTYPE##_ge(CNTYPE *i1, CNTYPE *i2) {\
        return convert_to_cn_bool(*(i1->val) >= *(i2->val));\
    }

#define CN_GEN_NEGATE(CNTYPE)\
    static inline CNTYPE *CNTYPE##_negate(CNTYPE *i) {\
        return convert_to_##CNTYPE(-(*i->val));\
    }


#define CN_GEN_ADD(CTYPE, CNTYPE)\
    static inline CNTYPE *CNTYPE##_add(CNTYPE *i1, CNTYPE *i2) {\
        CNTYPE *res = (CNTYPE *) alloc(sizeof(CNTYPE));\
        res->val = (CTYPE *) alloc(sizeof(CTYPE));\
        *(res->val) = *(i1->val) + *(i2->val);\
        return res;\
    }

#define CN_GEN_SUB(CTYPE, CNTYPE)\
    static inline CNTYPE *CNTYPE##_sub(CNTYPE *i1, CNTYPE *i2) {\
        CNTYPE *res = (CNTYPE *) alloc(sizeof(CNTYPE));\
        res->val = (CTYPE *) alloc(sizeof(CTYPE));\
        *(res->val) = *(i1->val) - *(i2->val);\
        return res;\
    }

#define CN_GEN_MUL(CTYPE, CNTYPE)\
    static inline CNTYPE *CNTYPE##_multiply(CNTYPE *i1, CNTYPE *i2) {\
        CNTYPE *res = (CNTYPE *) alloc(sizeof(CNTYPE));\
        res->val = (CTYPE *) alloc(sizeof(CTYPE));\
        *(res->val) = *(i1->val) * *(i2->val);\
        return res;\
    }

#define CN_GEN_DIV(CTYPE, CNTYPE)\
    static inline CNTYPE *CNTYPE##_divide(CNTYPE *i1, CNTYPE *i2) {\
        CNTYPE *res = (CNTYPE *) alloc(sizeof(CNTYPE));\
        res->val = (CTYPE *) alloc(sizeof(CTYPE));\
        *(res->val) = *(i1->val) / *(i2->val);\
        return res;\
    }

#define CN_GEN_SHIFT_LEFT(CTYPE, CNTYPE)\
    static inline CNTYPE *CNTYPE##_shift_left(CNTYPE *i1, CNTYPE *i2) {\
        CNTYPE *res = (CNTYPE *) alloc(sizeof(CNTYPE));\
        res->val = (CTYPE *) alloc(sizeof(CTYPE));\
        *(res->val) = *(i1->val) << *(i2->val);\
        return res;\
    }

#define CN_GEN_SHIFT_RIGHT(CTYPE, CNTYPE)\
    static inline CNTYPE *CNTYPE##_shift_right(CNTYPE *i1, CNTYPE *i2) {\
        CNTYPE *res = (CNTYPE *) alloc(sizeof(CNTYPE));\
        res->val = (CTYPE *) alloc(sizeof(CTYPE));\
        *(res->val) = *(i1->val) >> *(i2->val);\
        return res;\
    }

#define CN_GEN_MIN(CNTYPE)\
    static inline CNTYPE *CNTYPE##_min(CNTYPE *i1, CNTYPE *i2) {\
        return CNTYPE##_lt(i1, i2) ? i1 : i2;\
    }

#define CN_GEN_MAX(CNTYPE)\
    static inline CNTYPE *CNTYPE##_max(CNTYPE *i1, CNTYPE *i2) {\
        return CNTYPE##_gt(i1, i2) ? i1 : i2;\
    }

#define CN_GEN_MOD(CTYPE, CNTYPE)\
    static inline CNTYPE *CNTYPE##_mod(CNTYPE *i1, CNTYPE *i2) {\
        CNTYPE *res = (CNTYPE *) alloc(sizeof(CNTYPE));\
        res->val = (CTYPE *) alloc(sizeof(CTYPE));\
        *(res->val) = *(i1->val) % *(i2->val);\
        return res;\
    }

#define CN_GEN_XOR(CTYPE, CNTYPE)\
    static inline CNTYPE *CNTYPE##_xor(CNTYPE *i1, CNTYPE *i2) {\
        CNTYPE *res = (CNTYPE *) alloc(sizeof(CNTYPE));\
        res->val = (CTYPE *) alloc(sizeof(CTYPE));\
        *(res->val) = *(i1->val) ^ *(i2->val);\
        return res;\
    }

#define CN_GEN_BWAND(CTYPE, CNTYPE)\
    static inline CNTYPE *CNTYPE##_bwand(CNTYPE *i1, CNTYPE *i2) {\
        CNTYPE *res = (CNTYPE *) alloc(sizeof(CNTYPE));\
        res->val = (CTYPE *) alloc(sizeof(CTYPE));\
        *(res->val) = *(i1->val) & *(i2->val);\
        return res;\
    }

#define CN_GEN_BWOR(CTYPE, CNTYPE)\
    static inline CNTYPE *CNTYPE##_bwor(CNTYPE *i1, CNTYPE *i2) {\
        CNTYPE *res = (CNTYPE *) alloc(sizeof(CNTYPE));\
        res->val = (CTYPE *) alloc(sizeof(CTYPE));\
        *(res->val) = *(i1->val) | *(i2->val);\
        return res;\
    }

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
        CNTYPE *res = (CNTYPE *) alloc(sizeof(CNTYPE));\
        res->val = (CTYPE *) alloc(sizeof(CTYPE));\
        *(res->val) = ipow(*(i1->val), *(i2->val));\
        return res;\
    }


#define CN_GEN_ARRAY_SHIFT(CTYPE, CNTYPE)\
    static inline cn_pointer *cn_array_shift_##CNTYPE(cn_pointer *ptr, CNTYPE *i) {\
        cn_pointer *res = alloc(sizeof(cn_pointer));\
        res->ptr = (CTYPE *) ptr->ptr + (*(i->val) * sizeof(CTYPE));\
        return res;\
    }

/* 

member_shift<hyp_pool>(pool_pointer, free_area);

pool_pointer

*/

#define cn_member_shift(cn_ptr, tag, member_name)\
  convert_to_cn_pointer(&(((struct tag *) cn_ptr->ptr)->member_name))



#define CN_GEN_INCREMENT(CNTYPE)\
    static inline CNTYPE *CNTYPE##_increment(CNTYPE *i) {\
        *(i->val) = *(i->val) + 1;\
        return i;\
    }

#define CN_GEN_PTR_ADD(CNTYPE)\
    static inline cn_pointer *cn_pointer_add_##CNTYPE(cn_pointer *ptr, CNTYPE *i) {\
        cn_pointer *res = (cn_pointer *) alloc(sizeof(cn_pointer));\
        res->ptr = (char *) ptr->ptr + *(i->val);\
        return res;\
    }


/* Casting functions */

#define CN_GEN_CAST_TO_PTR(CNTYPE, INTPTR_TYPE)\
    static inline cn_pointer *cast_##CNTYPE##_to_cn_pointer(CNTYPE *i) {\
        cn_pointer *res = (cn_pointer *) alloc(sizeof(cn_pointer));\
        res->ptr = (void *) (INTPTR_TYPE) *(i->val);\
        return res;\
    }

#define CN_GEN_CAST_FROM_PTR(CTYPE, CNTYPE, INTPTR_TYPE)\
    static inline CNTYPE *cast_cn_pointer_to_##CNTYPE(cn_pointer *ptr) {\
        CNTYPE *res = (CNTYPE *) alloc(sizeof(CNTYPE));\
        res->val = (CTYPE *) alloc(sizeof(CTYPE));\
        *(res->val) = (CTYPE) (INTPTR_TYPE) (ptr->ptr);\
        return res;\
    }


#define CN_GEN_CAST_INT_TYPES(CNTYPE1, CTYPE2, CNTYPE2)\
    static inline CNTYPE2 *cast_##CNTYPE1##_to_##CNTYPE2(CNTYPE1 *i) {\
        CNTYPE2 *res = (CNTYPE2 *) alloc(sizeof(CNTYPE2));\
        res->val = (CTYPE2 *) alloc(sizeof(CTYPE2));\
        *(res->val) = (CTYPE2) *(i->val);\
        return res;\
    }



#define CN_GEN_CASTS_INNER(CTYPE, CNTYPE)\
    CN_GEN_CAST_INT_TYPES(cn_bits_i8, CTYPE, CNTYPE)\
    CN_GEN_CAST_INT_TYPES(cn_bits_i16, CTYPE, CNTYPE)\
    CN_GEN_CAST_INT_TYPES(cn_bits_i32, CTYPE, CNTYPE)\
    CN_GEN_CAST_INT_TYPES(cn_bits_i64, CTYPE, CNTYPE)\
    CN_GEN_CAST_INT_TYPES(cn_bits_u8, CTYPE, CNTYPE)\
    CN_GEN_CAST_INT_TYPES(cn_bits_u16, CTYPE, CNTYPE)\
    CN_GEN_CAST_INT_TYPES(cn_bits_u32, CTYPE, CNTYPE)\
    CN_GEN_CAST_INT_TYPES(cn_bits_u64, CTYPE, CNTYPE)\
    CN_GEN_CAST_INT_TYPES(cn_integer, CTYPE, CNTYPE)\


#define CN_GEN_PTR_CASTS_UNSIGNED(CTYPE, CNTYPE)\
    CN_GEN_CAST_TO_PTR(CNTYPE, uintptr_t)\
    CN_GEN_CAST_FROM_PTR(CTYPE, CNTYPE, uintptr_t)\

#define CN_GEN_PTR_CASTS_SIGNED(CTYPE, CNTYPE)\
    CN_GEN_CAST_TO_PTR(CNTYPE, intptr_t)\
    CN_GEN_CAST_FROM_PTR(CTYPE, CNTYPE, intptr_t)\


#define CN_GEN_ALL(CTYPE, CNTYPE)\
    CN_GEN_ALL_(CTYPE, CNTYPE)

#define CN_GEN_ALL_(CTYPE, CNTYPE)\
   CN_GEN_CONVERT(CTYPE, CNTYPE)\
   CN_GEN_CONVERT_FROM(CTYPE, CNTYPE)\
   CN_GEN_EQUALITY(CNTYPE)\
   CN_GEN_LT(CNTYPE)\
   CN_GEN_LE(CNTYPE)\
   CN_GEN_GT(CNTYPE)\
   CN_GEN_GE(CNTYPE)\
   CN_GEN_NEGATE(CNTYPE)\
   CN_GEN_ADD(CTYPE, CNTYPE)\
   CN_GEN_SUB(CTYPE, CNTYPE)\
   CN_GEN_MUL(CTYPE, CNTYPE)\
   CN_GEN_DIV(CTYPE, CNTYPE)\
   CN_GEN_SHIFT_LEFT(CTYPE, CNTYPE)\
   CN_GEN_SHIFT_RIGHT(CTYPE, CNTYPE)\
   CN_GEN_MIN(CNTYPE)\
   CN_GEN_MAX(CNTYPE)\
   CN_GEN_MOD(CTYPE, CNTYPE)\
   CN_GEN_XOR(CTYPE, CNTYPE)\
   CN_GEN_POW(CTYPE, CNTYPE)\
   CN_GEN_INCREMENT(CNTYPE)\
   CN_GEN_PTR_ADD(CNTYPE)\
   CN_GEN_CASTS_INNER(CTYPE, CNTYPE)\
   CN_GEN_ARRAY_SHIFT(CTYPE, CNTYPE)\

CN_GEN_ALL(signed char, cn_bits_i8)
CN_GEN_ALL(signed short, cn_bits_i16)
CN_GEN_ALL(signed long, cn_bits_i32)
CN_GEN_ALL(signed long long, cn_bits_i64)
CN_GEN_ALL(unsigned char, cn_bits_u8)
CN_GEN_ALL(unsigned short, cn_bits_u16)
CN_GEN_ALL(unsigned long, cn_bits_u32)
CN_GEN_ALL(unsigned long long, cn_bits_u64)
CN_GEN_ALL(signed long, cn_integer)


CN_GEN_PTR_CASTS_SIGNED(signed char, cn_bits_i8)
CN_GEN_PTR_CASTS_SIGNED(signed short, cn_bits_i16)
CN_GEN_PTR_CASTS_SIGNED(signed long, cn_bits_i32)
CN_GEN_PTR_CASTS_SIGNED(signed long long, cn_bits_i64)
CN_GEN_PTR_CASTS_UNSIGNED(unsigned char, cn_bits_u8)
CN_GEN_PTR_CASTS_UNSIGNED(unsigned short, cn_bits_u16)
CN_GEN_PTR_CASTS_UNSIGNED(unsigned long, cn_bits_u32)
CN_GEN_PTR_CASTS_UNSIGNED(unsigned long long, cn_bits_u64)
CN_GEN_PTR_CASTS_SIGNED(signed long, cn_integer)


cn_pointer *convert_to_cn_pointer(void *ptr);
cn_pointer *cn_pointer_add(cn_pointer *ptr, cn_integer *i);
cn_pointer *cast_cn_pointer_to_cn_pointer(cn_pointer *p);

/* OWNERSHIP */

enum OWNERSHIP {
    GET,
    PUT
};

int ghost_state_get(ownership_ghost_state *cn_ownership_global_ghost_state, signed long *address_key);
void ghost_state_set(ownership_ghost_state *cn_ownership_global_ghost_state, signed long* address_key, int stack_depth_val);
void ghost_state_remove(ownership_ghost_state *cn_ownership_global_ghost_state, signed long* address_key);

/* CN ownership checking */
void cn_get_ownership(uintptr_t generic_c_ptr, ownership_ghost_state *cn_ownership_global_ghost_state, size_t size, int cn_stack_depth, struct cn_error_message_info *error_msg_info);
void cn_put_ownership(uintptr_t generic_c_ptr, ownership_ghost_state *cn_ownership_global_ghost_state, size_t size, int cn_stack_depth, struct cn_error_message_info *error_msg_info);
void cn_check_ownership(enum OWNERSHIP owned_enum, uintptr_t generic_c_ptr, ownership_ghost_state *cn_ownership_global_ghost_state, size_t size, int cn_stack_depth, struct cn_error_message_info *error_msg_info);

/* C ownership checking */
// void c_add_local_to_ghost_state(uintptr_t ptr_to_local, ownership_ghost_state *cn_ownership_global_ghost_state, size_t size, int cn_stack_depth);
// void c_remove_local_from_ghost_state(uintptr_t ptr_to_local, ownership_ghost_state *cn_ownership_global_ghost_state, size_t size);

#define c_concat_with_mapping_stat(STAT, CTYPE, VAR_NAME, GHOST_STATE, STACK_DEPTH)\
    STAT; c_add_local_to_ghost_state((uintptr_t) &VAR_NAME, GHOST_STATE, sizeof(CTYPE), STACK_DEPTH);

#define c_declare_and_map_local(CTYPE, VAR_NAME)\
    c_concat_with_mapping_stat(CTYPE VAR_NAME, CTYPE, VAR_NAME)

#define c_declare_init_and_map_local(CTYPE, VAR_NAME, EXPR)\
    c_concat_with_mapping_stat(CTYPE VAR_NAME = EXPR, CTYPE, VAR_NAME)


void cn_load(void *lvalue, size_t size);
void cn_store(void *lvalue, size_t size);

#define CN_LOAD(LV) \
  ({ \
    cn_load(&LV, sizeof(typeof(LV))); \
    (LV); \
  })
#define CN_STORE(LV, X) \
 ({ \
    typeof(LV) *tmp; \
    tmp = &(LV); \
    cn_store(&LV, sizeof(typeof(LV))); \
    *tmp = (X); \
 })
