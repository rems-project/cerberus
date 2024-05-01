#include "hash_table.h"
#include <stdio.h>
#include <stdlib.h>
// #include <math.h>
// #include <assert.h>
#include "stdint.h"

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

/* Conversion functions */

cn_bool *convert_to_cn_bool(_Bool b);
_Bool convert_from_cn_bool(cn_bool *b);
void cn_assert(cn_bool *cn_b, const char *function_name, char *file_name, int line_number);

cn_bool *cn_bool_and(cn_bool *b1, cn_bool *b2);
cn_bool *cn_bool_or(cn_bool *b1, cn_bool *b2);
cn_bool *cn_bool_not(cn_bool *b);
cn_bool *cn_bool_equality(cn_bool *b1, cn_bool *b2);
void *cn_ite(cn_bool *b, void *e1, void *e2);

cn_map *map_create(void);
void *cn_map_get(cn_map *m, cn_integer *key);
void cn_map_set(cn_map *m, cn_integer *key, void *value);
cn_bool *cn_map_equality(cn_map *m1, cn_map *m2, cn_bool *(value_equality_fun)(void *, void *));

cn_bool *cn_pointer_equality(void *i1, void *i2);

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
   CN_GEN_EQUALITY(CNTYPE)\
   CN_GEN_LT(CNTYPE)\
   CN_GEN_LE(CNTYPE)\
   CN_GEN_GT(CNTYPE)\
   CN_GEN_GE(CNTYPE)\
   CN_GEN_ADD(CTYPE, CNTYPE)\
   CN_GEN_SUB(CTYPE, CNTYPE)\
   CN_GEN_MUL(CTYPE, CNTYPE)\
   CN_GEN_DIV(CTYPE, CNTYPE)\
   CN_GEN_MIN(CNTYPE)\
   CN_GEN_MAX(CNTYPE)\
   CN_GEN_MOD(CTYPE, CNTYPE)\
   CN_GEN_POW(CTYPE, CNTYPE)\
   CN_GEN_INCREMENT(CNTYPE)\
   CN_GEN_PTR_ADD(CNTYPE)\
   CN_GEN_CASTS_INNER(CTYPE, CNTYPE)\


CN_GEN_ALL(signed char, cn_bits_i8);
CN_GEN_ALL(signed short, cn_bits_i16);
CN_GEN_ALL(signed long, cn_bits_i32);
CN_GEN_ALL(signed long long, cn_bits_i64);
CN_GEN_ALL(unsigned char, cn_bits_u8);
CN_GEN_ALL(unsigned short, cn_bits_u16);
CN_GEN_ALL(unsigned long, cn_bits_u32);
CN_GEN_ALL(unsigned long long, cn_bits_u64);
CN_GEN_ALL(signed long, cn_integer);


CN_GEN_PTR_CASTS_SIGNED(signed char, cn_bits_i8);
CN_GEN_PTR_CASTS_SIGNED(signed short, cn_bits_i16);
CN_GEN_PTR_CASTS_SIGNED(signed long, cn_bits_i32);
CN_GEN_PTR_CASTS_SIGNED(signed long long, cn_bits_i64);
CN_GEN_PTR_CASTS_UNSIGNED(unsigned char, cn_bits_u8);
CN_GEN_PTR_CASTS_UNSIGNED(unsigned short, cn_bits_u16);
CN_GEN_PTR_CASTS_UNSIGNED(unsigned long, cn_bits_u32);
CN_GEN_PTR_CASTS_UNSIGNED(unsigned long long, cn_bits_u64);
CN_GEN_PTR_CASTS_SIGNED(signed long, cn_integer);


cn_pointer *convert_to_cn_pointer(void *ptr);
cn_pointer *cn_pointer_add(cn_pointer *ptr, cn_integer *i);

// Ownership
enum OWNERSHIP {
    GET,
    TAKE
};
