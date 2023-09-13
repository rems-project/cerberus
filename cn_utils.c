
// #include "alloc.c"
#include "hash_table.c"



/* Wrappers for C types */

typedef signed long cn_integer;
typedef _Bool cn_bool;

_Bool cn_char_equality(void *a, void *b) {
    return *(char *)a == *(char *)b;
}

typedef hash_table cn_map;


void *cn_map_get(cn_map *m, const char key) {
    const char key_arr[1] = {key};
    return ht_get(m, key_arr);
}

void cn_map_set(cn_map *m, const char key, void *value) {
    const char key_arr[1] = {key};
    ht_set(m, key_arr, value);
}

/* Every equality function needs to take two void pointers for this to work */
_Bool cn_integer_equality(void *i1, void *i2) {
    return *((cn_integer *) i1) == *((cn_integer *) i2);
}

_Bool cn_map_equality(cn_map *m1, cn_map *m2, _Bool (value_equality_fun)(void *, void *)) {
    if (ht_size(m1) != ht_size(m2)) return 0;
    
    hash_table_iterator hti1 = ht_iterator(m1);
    hash_table_iterator hti2 = ht_iterator(m2);

    while (ht_next(&hti1) && ht_next(&hti2)) {
        if (!value_equality_fun(hti1.value, hti2.value)) return 0;
    }

    return 1;
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

cn_integer *convert_to_cn_integer(char c) {
    cn_integer *ret = alloc(sizeof(cn_integer));
    *ret = (cn_integer) c;
    return ret;
}
