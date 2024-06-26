
// #include "alloc.c"
#include <cn-executable/utils.h>
#include <signal.h> // for SIGABRT

/*

typedef struct cn_bool {
    _Bool val;
} cn_bool;

*/


void cn_exit_aux(void) {
    exit(SIGABRT);
}

void (*cn_exit)(void) = &cn_exit_aux;


cn_bool *convert_to_cn_bool(_Bool b) {
    cn_bool *res = alloc(sizeof(cn_bool));
    if (!res) exit(1);
    // printf("%p\n", (void *) res);
    // printf("%p\n", (void *) &(res->val));
    res->val = b;
    return res;
}

_Bool convert_from_cn_bool(cn_bool *b) {
    return b->val;
}

void cn_assert(cn_bool *cn_b, struct cn_error_message_info *error_msg_info) {
    if (!(cn_b->val)) {
        printf("CN assertion failed: function %s, file %s, line %d\n.", error_msg_info->function_name, error_msg_info->file_name, error_msg_info->line_number);
        if (error_msg_info->cn_source_loc) {
            printf("CN source location: \n%s\n", error_msg_info->cn_source_loc);
        }
        cn_exit();
    }
    // assert(cn_b->val);
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

void *cn_ite(cn_bool *b, void *e1, void *e2) {
    return b->val ? e1 : e2;
}


cn_map *map_create(void) {
    return ht_create();
}

ownership_ghost_state *initialise_ownership_ghost_state(void) {
    return ht_create();
}

int ghost_state_get(ownership_ghost_state *cn_ownership_global_ghost_state, signed long *address_key) {
    int *curr_depth_maybe = (int *) ht_get(cn_ownership_global_ghost_state, address_key);
    return curr_depth_maybe ? *curr_depth_maybe : -1;
}

void ghost_state_set(ownership_ghost_state *cn_ownership_global_ghost_state, signed long* address_key, int stack_depth_val) {
    int *new_depth = alloc(sizeof(int));
    *new_depth = stack_depth_val;
    ht_set(cn_ownership_global_ghost_state, address_key, new_depth);
}

void ghost_state_remove(ownership_ghost_state *cn_ownership_global_ghost_state, signed long* address_key) {
    ghost_state_set(cn_ownership_global_ghost_state, address_key, -1);
}

void cn_get_ownership(uintptr_t generic_c_ptr, ownership_ghost_state *cn_ownership_global_ghost_state, size_t size, int cn_stack_depth, struct cn_error_message_info *error_msg_info) {
    for (int i = 0; i < size; i++) {
        signed long *address_key = alloc(sizeof(long));
        // printf("Getting ownership for: %lu\n", generic_c_ptr + i);
        *address_key = generic_c_ptr + i;
        int curr_depth = ghost_state_get(cn_ownership_global_ghost_state, address_key);
        cn_assert(convert_to_cn_bool(curr_depth == cn_stack_depth - 1), error_msg_info);
        ghost_state_set(cn_ownership_global_ghost_state, address_key, cn_stack_depth);
    }
}

void cn_put_ownership(uintptr_t generic_c_ptr, ownership_ghost_state *cn_ownership_global_ghost_state, size_t size, int cn_stack_depth, struct cn_error_message_info *error_msg_info) {
    for (int i = 0; i < size; i++) { 
        signed long *address_key = alloc(sizeof(long));
        *address_key = generic_c_ptr + i;
        int curr_depth = ghost_state_get(cn_ownership_global_ghost_state, address_key);
        cn_assert(convert_to_cn_bool(curr_depth == cn_stack_depth), error_msg_info);
        ghost_state_set(cn_ownership_global_ghost_state, address_key, cn_stack_depth - 1);
    }
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


cn_bool *cn_pointer_equality(void *i1, void *i2) {
    return convert_to_cn_bool((((cn_pointer *) i1)->ptr) == (((cn_pointer *) i2)->ptr));
}

cn_bool *cn_pointer_is_null(cn_pointer *p) {
    return convert_to_cn_bool(p->ptr == NULL);
}



// Check if m2 is a subset of m1
cn_bool *cn_map_subset(cn_map *m1, cn_map *m2, cn_bool *(value_equality_fun)(void *, void *)) {
    if (ht_size(m1) != ht_size(m2)) return convert_to_cn_bool(0);
    
    hash_table_iterator hti1 = ht_iterator(m1);

    while (ht_next(&hti1)) {
        signed long* curr_key = hti1.key;
        void *val1 = ht_get(m1, curr_key);
        void *val2 = ht_get(m2, curr_key);

        /* Check if other map has this key at all */
        if (!val2) return convert_to_cn_bool(0);

        if (convert_from_cn_bool(cn_bool_not(value_equality_fun(val1, val2)))) {
            printf("Values not equal!\n");
            return convert_to_cn_bool(0);
        } 
    }

    return convert_to_cn_bool(1);
}

cn_bool *cn_map_equality(cn_map *m1, cn_map *m2, cn_bool *(value_equality_fun)(void *, void *)) {
    return cn_bool_and(cn_map_subset(m1, m2, value_equality_fun), cn_map_subset(m2, m1, value_equality_fun));
}



cn_pointer *convert_to_cn_pointer(void *ptr) {
    cn_pointer *res = (cn_pointer *) alloc(sizeof(cn_pointer));
    res->ptr = ptr; // Carries around an address
    return res;
}

/*
struct cn_error_message_info {
    const char *function_name;
    char *file_name;
    int line_number;
    char *cn_source_loc;
};
*/

void update_error_message_info_(struct cn_error_message_info *error_msg_info, const char *function_name, char *file_name, int line_number, char *cn_source_loc) {
    error_msg_info->function_name = function_name;
    error_msg_info->file_name = file_name;
    error_msg_info->line_number = line_number;
    error_msg_info->cn_source_loc = cn_source_loc;
}



/* CN: addr_eq(ptr1: cn_pointer, ptr2: cn_pointer) */
/* Internal CN: cn_pointer_to_bitvector_cast(ptr1) == cn_pointer_to_bitvector_cast(ptr2) */
/* C: 
    cn_pointer *ptr1_cn = convert_to_cn_pointer(ptr1);
    cn_pointer *ptr2_cn = convert_to_cn_pointer(ptr2);

    cn_assert(convert_to_cn_bool(cast_cn_pointer_to_bitvector(ptr1_cn) == cast_cn_pointer_to_bitvector(ptr2_cn)));
*/
