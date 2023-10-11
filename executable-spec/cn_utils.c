
// #include "alloc.c"
#include "hash_table.c"
#include <stdio.h>


/* Wrappers for C types */

// typedef unsigned int cn_integer_2;

// cn_integer_2 *convert_to_cn_integer_2(unsigned int i) {
//     cn_integer_2 *cn_i = alloc(sizeof(cn_integer_2));
//     *cn_i = i;
//     return cn_i;
// }


typedef struct cn_integer {
    unsigned int *val;
} cn_integer;

typedef struct cn_pointer {
    void *ptr;
} cn_pointer;

typedef _Bool cn_bool;

_Bool cn_char_equality(void *a, void *b) {
    return *(char *)a == *(char *)b;
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

// void *cn_map_get_2(cn_map *m, cn_integer_2 *key) {
//     // const char key_arr[1] = {key};
//     void *res = ht_get(m, key);
//     if (!res) printf("NULL being returned for key %d\n", *(key));
//     return res;
// }

// void cn_map_set_2(cn_map *m, cn_integer_2 *key, void *value) {
//     ht_set(m, key, value);
// }

/* Every equality function needs to take two void pointers for this to work */
_Bool cn_integer_equality(void *i1, void *i2) {
    return (*((cn_integer *) i1)->val) == (*((cn_integer *) i2)->val);
}



// Check if m2 is a subset of m1
_Bool cn_map_subset(cn_map *m1, cn_map *m2, _Bool (value_equality_fun)(void *, void *)) {
    if (ht_size(m1) != ht_size(m2)) return 0;
    
    hash_table_iterator hti1 = ht_iterator(m1);

    while (ht_next(&hti1)) {
        unsigned int* curr_key = hti1.key;
        void *val1 = ht_get(m1, curr_key);
        void *val2 = ht_get(m2, curr_key);

        /* Check if other map has this key at all */
        if (!val2) return 0;

        if (!value_equality_fun(val1, val2)) {
            printf("Values not equal!\n");
            return 0;
        } 
    }

    return 1;
}

_Bool cn_map_equality(cn_map *m1, cn_map *m2, _Bool (value_equality_fun)(void *, void *)) {
    return cn_map_subset(m1, m2, value_equality_fun) && cn_map_subset(m2, m1, value_equality_fun);
}




/* Generic CN equality function */

// _Bool cn_arr_equality(struct cn_array *a, struct cn_array *b) {
//     if (a->num_elements != b->num_elements) return 0;
//     if (a->element_type != b->element_type) return 0;


//     for (int i = 0; i < a->num_elements; i++) {
        
//     }

//     return 1;
// }



long min(long a, long b) {
    return a < b ? a : b;
}

long max(long a, long b) {
    return a > b ? a : b;
}

// int array_size(char a[]) {
//     /* Current invariant: arrays are non-empty */
//     return (sizeof a)  / (sizeof a[0]);
// }

// _Bool cn_equality_chars(char *a, char* b) {
//     /* Current invariant: arrays are non-empty */
//     if (array_size(a) != array_size(b)) {
//         return 0;
//     }

//     for (int i = 0; i < array_size(a); i++) {
//         if (a[i] != b[i]) {
//             return 0;
//         }
//     }

//     return 1;
// }

/* Conversion functions */

cn_integer *convert_to_cn_integer(unsigned int i) {
    cn_integer *ret = alloc(sizeof(cn_integer));
    // unsigned int *i_ptr = alloc(sizeof(unsigned int));
    // *i_ptr = i;
    // ret->val = i_ptr;
    ret->val = alloc(sizeof(unsigned int));
    *(ret->val) = i;
    // ret->val = i;
    return ret;
}

cn_pointer *convert_to_cn_pointer(void *ptr) {
    cn_pointer *res = alloc(sizeof(cn_pointer));
    res->ptr = ptr; // Carries around an address
    return res;
}

/* These should be produced automatically based on binops used in source CN annotations */
cn_bool cn_integer_lt(cn_integer *i1, cn_integer *i2) {
    return *(i1->val) < *(i2->val);
}

cn_bool cn_integer_le(cn_integer *i1, cn_integer *i2) {
    return *(i1->val) <= *(i2->val);
}

cn_bool cn_integer_gt(cn_integer *i1, cn_integer *i2) {
    return *(i1->val) > *(i2->val);
}

cn_bool cn_integer_ge(cn_integer *i1, cn_integer *i2) {
    return *(i1->val) >= *(i2->val);
}

cn_integer *cn_integer_add(cn_integer *i1, cn_integer *i2) {
    cn_integer *res = alloc(sizeof(cn_integer));
    res->val = alloc(sizeof(unsigned int));
    *(res->val) = *(i1->val) + *(i2->val);
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

char owned_char(cn_pointer *cn_pointer, enum OWNERSHIP owned_enum) {
    switch (owned_enum) {
        case GET:
            // printf("GET case\n");
            break;
        case TAKE:
            // printf("TAKE case\n");
            break;
    }
    return *((char *) cn_pointer->ptr);
}

