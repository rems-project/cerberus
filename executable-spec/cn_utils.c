
// #include "alloc.c"
#include "hash_table.c"
#include <stdio.h>
#include <math.h>
#include <assert.h>


/* Wrappers for C types */


typedef struct cn_integer {
    unsigned int *val;
} cn_integer;

typedef struct cn_pointer {
    void *ptr;
} cn_pointer;

typedef struct cn_bool {
    _Bool val;
} cn_bool;

cn_bool *convert_to_cn_bool(_Bool b) {
    cn_bool *res = alloc(sizeof(cn_bool));
    res->val = b;
    return res;
}

void cn_assert(cn_bool *cn_b) {
    assert(cn_b->val);
}

cn_bool *cn_bool_and(cn_bool *b1, cn_bool *b2) {
    cn_bool *res = alloc(sizeof(cn_bool));
    res->val = b1->val && b2->val;
    return res;
}

cn_bool *cn_bool_or(cn_bool *b1, cn_bool *b2) {
    cn_bool *res = alloc(sizeof(cn_bool));
    res->val = b1->val || b2->val;
    return res;
}

cn_bool *cn_bool_not(cn_bool *b) {
    cn_bool *res = alloc(sizeof(cn_bool));
    res->val = !(b->val);
    return res;
}

cn_bool *cn_bool_equality(cn_bool *b1, cn_bool *b2) {
    return convert_to_cn_bool(b1->val == b2->val);
}


typedef hash_table cn_map;

cn_map *map_create(void) {
    return ht_create();
}


void *cn_map_get(cn_map *m, cn_integer *key) {
    // const char key_arr[1] = {key};
    void *res = ht_get(m, key->val);
    // if (!res) printf("NULL being returned for key %d\n", *(key->val));
    return res;
}

void cn_map_set(cn_map *m, cn_integer *key, void *value) {
    ht_set(m, key->val, value);
}

/* Every equality function needs to take two void pointers for this to work */
cn_bool *cn_integer_equality(void *i1, void *i2) {
    return convert_to_cn_bool((*((cn_integer *) i1)->val) == (*((cn_integer *) i2)->val));
}

cn_bool *cn_pointer_equality(void *i1, void *i2) {
    return convert_to_cn_bool((((cn_pointer *) i1)->ptr) == (((cn_pointer *) i2)->ptr));
}


// Check if m2 is a subset of m1
cn_bool *cn_map_subset(cn_map *m1, cn_map *m2, _Bool (value_equality_fun)(void *, void *)) {
    if (ht_size(m1) != ht_size(m2)) return convert_to_cn_bool(0);
    
    hash_table_iterator hti1 = ht_iterator(m1);

    while (ht_next(&hti1)) {
        unsigned int* curr_key = hti1.key;
        void *val1 = ht_get(m1, curr_key);
        void *val2 = ht_get(m2, curr_key);

        /* Check if other map has this key at all */
        if (!val2) return convert_to_cn_bool(0);

        if (!value_equality_fun(val1, val2)) {
            printf("Values not equal!\n");
            return convert_to_cn_bool(0);
        } 
    }

    return convert_to_cn_bool(1);
}

cn_bool *cn_map_equality(cn_map *m1, cn_map *m2, _Bool (value_equality_fun)(void *, void *)) {
    return cn_bool_and(cn_map_subset(m1, m2, value_equality_fun), cn_map_subset(m2, m1, value_equality_fun));
}




/* Conversion functions */

cn_integer *convert_to_cn_integer(unsigned int i) {
    cn_integer *ret = alloc(sizeof(cn_integer));
    ret->val = alloc(sizeof(unsigned int));
    *(ret->val) = i;
    return ret;
}

cn_pointer *convert_to_cn_pointer(void *ptr) {
    cn_pointer *res = alloc(sizeof(cn_pointer));
    res->ptr = ptr; // Carries around an address
    return res;
}

/* These should be produced automatically based on binops used in source CN annotations */
cn_bool *cn_integer_lt(cn_integer *i1, cn_integer *i2) {
    return convert_to_cn_bool(*(i1->val) < *(i2->val));
}

cn_bool *cn_integer_le(cn_integer *i1, cn_integer *i2) {
    return convert_to_cn_bool(*(i1->val) <= *(i2->val));
}

cn_bool *cn_integer_gt(cn_integer *i1, cn_integer *i2) {
    return convert_to_cn_bool(*(i1->val) > *(i2->val));
}

cn_bool *cn_integer_ge(cn_integer *i1, cn_integer *i2) {
    return convert_to_cn_bool(*(i1->val) >= *(i2->val));
}

cn_integer *cn_integer_add(cn_integer *i1, cn_integer *i2) {
    cn_integer *res = alloc(sizeof(cn_integer));
    res->val = alloc(sizeof(unsigned int));
    *(res->val) = *(i1->val) + *(i2->val);
    return res;
}

cn_integer *cn_integer_sub(cn_integer *i1, cn_integer *i2) {
    cn_integer *res = alloc(sizeof(cn_integer));
    res->val = alloc(sizeof(unsigned int));
    *(res->val) = *(i1->val) - *(i2->val);
    return res;
}

cn_integer *cn_integer_pow(cn_integer *i1, cn_integer *i2) {
    cn_integer *res = alloc(sizeof(cn_integer));
    res->val = alloc(sizeof(unsigned int));
    *(res->val) = pow(*(i1->val), *(i2->val));
    return res;
}

cn_integer *cn_integer_increment(cn_integer *i) {
    *(i->val) = *(i->val) + 1;
    return i;
}

cn_integer *cn_integer_multiply(cn_integer *i1, cn_integer *i2) {
    cn_integer *res = alloc(sizeof(cn_integer));
    res->val = alloc(sizeof(unsigned int));
    *(res->val) = *(i1->val) * *(i2->val);
    return res;
}

cn_integer *cn_integer_divide(cn_integer *i1, cn_integer *i2) {
    cn_integer *res = alloc(sizeof(cn_integer));
    res->val = alloc(sizeof(unsigned int));
    *(res->val) = *(i1->val) / *(i2->val);
    return res;
}

cn_integer *cn_integer_mod(cn_integer *i1, cn_integer *i2) {
    cn_integer *res = alloc(sizeof(cn_integer));
    res->val = alloc(sizeof(unsigned int));
    *(res->val) = *(i1->val) % *(i2->val);
    return res;
}

cn_integer *cn_integer_min(cn_integer *i1, cn_integer *i2) {
    return cn_integer_lt(i1, i2) ? i1 : i2;
}

cn_integer *cn_integer_max(cn_integer *i1, cn_integer *i2) {
    return cn_integer_gt(i1, i2) ? i1 : i2;
}


cn_pointer *cn_pointer_add(cn_pointer *ptr, cn_integer *i) {
    cn_pointer *res = alloc(sizeof(cn_pointer));
    res->ptr = (char *) ptr->ptr + *(i->val);
    return res;
}

// Ownership functions

enum OWNERSHIP {
    GET,
    TAKE
};



cn_integer *cast_cn_pointer_to_cn_integer(cn_pointer *ptr) {
    cn_integer *res = alloc(sizeof(cn_integer));
    res->val = alloc(sizeof(unsigned int));
    *(res->val) = (unsigned int) ptr->ptr;
    return res;
}

cn_pointer *cast_cn_integer_to_cn_pointer(cn_integer *i) {
    cn_pointer *res = alloc(sizeof(cn_pointer));
    res->ptr = (void *) *(i->val);
    return res;
}
