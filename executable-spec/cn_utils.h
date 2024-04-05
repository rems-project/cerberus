#include "hash_table.h"
#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <assert.h>

/* Wrappers for C types */

typedef struct cn_bits_i32 {
    signed long *val;
} cn_bits_i32;

typedef struct cn_bits_i64 {
    signed long long *val;
} cn_bits_i64;

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

cn_bool *cn_bits_i32_equality(void *i1, void *i2);
cn_bool *cn_bits_i64_equality(void *i1, void *i2);
cn_bool *cn_bits_u32_equality(void *i1, void *i2);
cn_bool *cn_bits_u64_equality(void *i1, void *i2);
cn_bool *cn_integer_equality(void *i1, void *i2);
cn_bool *cn_pointer_equality(void *i1, void *i2);

cn_bool *cn_map_equality(cn_map *m1, cn_map *m2, cn_bool *(value_equality_fun)(void *, void *));

cn_bits_i32 *convert_to_cn_bits_i32(signed long i);
cn_bits_i64 *convert_to_cn_bits_i64(signed long long i);
cn_bits_u32 *convert_to_cn_bits_u32(unsigned long i);
cn_bits_u32 *convert_to_cn_bits_u64(unsigned long long i);
cn_integer *convert_to_cn_integer(signed long i);
cn_pointer *convert_to_cn_pointer(void *ptr);
cn_bool *cn_bits_i32_lt(cn_bits_i32 *i1, cn_bits_i32 *i2);
cn_bool *cn_integer_lt(cn_integer *i1, cn_integer *i2);
cn_bool *cn_integer_le(cn_integer *i1, cn_integer *i2);
cn_bool *cn_integer_gt(cn_integer *i1, cn_integer *i2);
cn_bool *cn_integer_ge(cn_integer *i1, cn_integer *i2);

cn_bits_i32 *cn_bits_i32_add(cn_bits_i32 *i1, cn_bits_i32 *i2);
cn_integer *cn_integer_add(cn_integer *i1, cn_integer *i2);
cn_integer *cn_integer_sub(cn_integer *i1, cn_integer *i2);
cn_integer *cn_integer_pow(cn_integer *i1, cn_integer *i2);
cn_integer *cn_integer_increment(cn_integer *i);
cn_integer *cn_integer_multiply(cn_integer *i1, cn_integer *i2);
cn_integer *cn_integer_divide(cn_integer *i1, cn_integer *i2);
cn_integer *cn_integer_mod(cn_integer *i1, cn_integer *i2);
cn_integer *cn_integer_min(cn_integer *i1, cn_integer *i2);
cn_integer *cn_integer_max(cn_integer *i1, cn_integer *i2);
cn_pointer *cn_pointer_add(cn_pointer *ptr, cn_integer *i);

// Ownership functions
enum OWNERSHIP {
    GET,
    TAKE
};

cn_bits_u64 *cast_cn_pointer_to_cn_bits_u64(cn_pointer *ptr);
cn_integer *cast_cn_pointer_to_cn_integer(cn_pointer *ptr);
cn_pointer *cast_cn_integer_to_cn_pointer(cn_integer *i);