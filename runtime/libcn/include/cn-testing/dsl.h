#ifndef CN_GEN_DSL_H
#define CN_GEN_DSL_H

#include <stdio.h>

#include "backtrack.h"


#define CN_GEN_INIT()                                                                   \
    if (0) {                                                                            \
    cn_label_bennet_backtrack:                                                          \
        return NULL;                                                                    \
    }

#define CN_GEN_UNIFORM(ty, sz) cn_gen_uniform_##ty(sz)

#define CN_GEN_RANGE(ty, min, max) cn_gen_range_##ty(min, max)

#define CN_GEN_MULT_RANGE(ty, mul, min, max) cn_gen_mult_range_##ty(mul, min, max)

#define CN_GEN_MULT(ty, mul) cn_gen_mult_##ty(mul)

#define CN_GEN_ASSIGN(p, offset, addr_ty, value, tmp, gen_name, last_var)               \
    cn_bits_u64* __##p##_size = cn_bits_u64_add(                                        \
                offset,  \
                convert_to_cn_bits_u64(sizeof(addr_ty)));                               \
    if (!convert_from_cn_bool(cn_bits_u64_le(__##p##_size, cn_gen_alloc_size(p)))) {    \
        cn_gen_backtrack_relevant_add((char*)#p);                                       \
        cn_gen_backtrack_alloc_set(convert_from_cn_bits_u64(__##p##_size));             \
        goto cn_label_##last_var##_backtrack;                                           \
    }                                                                                   \
    void *tmp = convert_from_cn_pointer(cn_pointer_add_cn_bits_u64(p, offset));         \
    *(addr_ty*)tmp = value;                                                             \
    cn_assume_ownership(tmp, sizeof(addr_ty), (char*)gen_name);

#define CN_GEN_LET_BEGIN(backtracks, var)                                               \
    int var##_backtracks = backtracks;                                                  \
    cn_label_##var##_gen:                                                               \
        ;

#define CN_GEN_LET_BODY(ty, var, gen)                                                   \
        ty* var = gen;

#define CN_GEN_LET_FROM(...)                                                            \
        {                                                                               \
            char* from[] = { __VA_ARGS__, NULL };

#define CN_GEN_LET_TO(...)                                                              \
            char* to[] = { __VA_ARGS__, NULL };                                         \
            cn_gen_backtrack_relevant_remap_many(from, to);                             \
        }

#define CN_GEN_LET_END(backtracks, var, last_var, ...)                                  \
        if (cn_gen_backtrack_type() != CN_GEN_BACKTRACK_NONE) {                         \
        cn_label_##var##_backtrack:                                                     \
            if (cn_gen_backtrack_relevant_contains((char*)#var)) {                      \
                char *toAdd[] = { __VA_ARGS__ };                                        \
                cn_gen_backtrack_relevant_add_many(toAdd);                              \
                if (var##_backtracks <= 0) {                                            \
                    goto cn_label_##last_var##_backtrack;                               \
                }                                                                       \
                if (cn_gen_backtrack_type() == CN_GEN_BACKTRACK_ASSERT) {               \
                    var##_backtracks--;                                                 \
                    cn_gen_backtrack_reset();                                           \
                }                                                                       \
                goto cn_label_##var##_gen;                                              \
            } else {                                                                    \
                goto cn_label_##last_var##_backtrack;                                   \
            }                                                                           \
        }

// #define CN_GEN_RETURN(val) val

#define CN_GEN_ASSERT(cond, last_var, ...)                                              \
    if (!convert_from_cn_bool(cond)) {                                                  \
        cn_gen_backtrack_assert_failure();                                              \
        char *toAdd[] = { __VA_ARGS__ };                                                \
        cn_gen_backtrack_relevant_add_many(toAdd);                                      \
        goto cn_label_##last_var##_backtrack;                                           \
    }

#define CN_GEN_MAP_BEGIN(map, i, i_ty, min, max)                                        \
    cn_map* map = map_create();                                                         \
    {                                                                                   \
        i_ty* i = max;                                                                  \
        while (convert_from_cn_bool(i_ty##_ge(i, min))) {

#define CN_GEN_MAP_BODY(perm)                                                           \
            if (convert_from_cn_bool(perm)) {

#define CN_GEN_MAP_END(map, i, i_ty, min, val)                                          \
                cn_map_set(map, cast_##i_ty##_to_cn_integer(i), val);                   \
            }                                                                           \
            if (convert_from_cn_bool(i_ty##_equality(i, min))) {                        \
                break;                                                                  \
            }                                                                           \
            i = i_ty##_sub(i, convert_to_##i_ty(1));                                    \
        }                                                                               \
    }

#endif // CN_GEN_DSL_H
