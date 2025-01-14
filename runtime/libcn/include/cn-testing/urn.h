#ifndef CN_GEN_URN_H
#define CN_GEN_URN_H

#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

    struct cn_gen_int_tree {
        uint64_t weight;
        uint64_t value;

        struct cn_gen_int_tree* left;
        struct cn_gen_int_tree* right;
    };

    struct cn_gen_int_urn {
        uint8_t size;
        struct cn_gen_int_tree* tree;
    };

    struct cn_gen_int_urn* urn_from_array(uint64_t elems[], uint8_t len);

    void urn_insert(struct cn_gen_int_urn* urn, uint64_t weight, uint64_t value);

    uint64_t urn_remove(struct cn_gen_int_urn* urn);

    void urn_free(struct cn_gen_int_urn* urn);

#ifdef __cplusplus
}
#endif

#endif // CN_GEN_URN_H
