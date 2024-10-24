#ifndef CN_GEN_URN_H
#define CN_GEN_URN_H

#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

    struct int_tree {
        uint64_t weight;
        uint64_t value;

        struct int_tree* left;
        struct int_tree* right;
    };

    struct int_urn {
        uint8_t size;
        struct int_tree* tree;
    };

    struct int_urn* urn_from_array(uint64_t elems[], uint8_t len);

    void urn_insert(struct int_urn* urn, uint64_t weight, uint64_t value);

    uint64_t urn_remove(struct int_urn* urn);

    void urn_free(struct int_urn* urn);

#ifdef __cplusplus
}
#endif

#endif // CN_GEN_URN_H
