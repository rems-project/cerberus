#include <stdio.h>


static const signed int MEM_SIZE = 10000;
char buf[MEM_SIZE];
static void *curr = buf;

/* Allocation function */
void *alloc(long nbytes) {
    void *res = curr;
    curr += nbytes;
    return res;
}

enum cn_type_enum {
    UNIT,
    BOOL,
    INTEGER,
    REAL,
    ARRAY,
    MAP
};

/* Wrappers for C types */

struct cn_array {
    enum cn_type_enum element_type;
    int num_elements;
    void *elements;
};

struct cn_map {
    enum cn_type_enum key_type;
    enum cn_type_enum value_type;
    /* TODO: Implement hash table */
};

struct cn_data_structure {
    enum cn_type_enum cn_type;
    union {
        signed int i;
        _Bool b;
        struct cn_array *arr;
        struct cn_map *map;
    } ds_u;
};



struct cn_data_structure *cn_bool(_Bool b) {
    struct cn_data_structure *bool_ds = alloc(sizeof(struct cn_data_structure));
    bool_ds->cn_type = BOOL;
    bool_ds->ds_u.b = b;
    return bool_ds;
}

struct cn_data_structure *cn_integer(signed int i) {
    struct cn_data_structure *integer_ds = alloc(sizeof(struct cn_data_structure));
    integer_ds->cn_type = INTEGER;
    integer_ds->ds_u.i = i;
    return integer_ds;
}

struct cn_data_structure *cn_array(void *arr_elements, int num_elements, enum cn_type_enum element_type) {
    struct cn_array *cn_arr = alloc(sizeof(struct cn_array));
    cn_arr->elements = arr_elements;
    cn_arr->num_elements = num_elements;
    cn_arr->element_type = element_type;
    struct cn_data_structure *arr_ds = alloc(sizeof(struct cn_data_structure));
    arr_ds->cn_type = ARRAY;
    arr_ds->ds_u.arr = cn_arr;
    return arr_ds;
}

/* Generic CN equality function */
_Bool cn_equality(void *a, void *b) {
    struct cn_data_structure *cn_a = (struct cn_data_structure *) a;
    struct cn_data_structure *cn_b = (struct cn_data_structure *) b;

    if (cn_a->cn_type != cn_b->cn_type) return 0;

    switch (cn_a->cn_type) {
        case UNIT:
            return 1;
        case BOOL:
            return cn_a->ds_u.b == cn_b->ds_u.b;
        case INTEGER:
            return 1;
        case REAL:
            return 1;
        case ARRAY:
            return 1;
        case MAP:
            return 1;
        default:
            return 0; 
    }
}


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


int main(void) {
    return 0;
}
