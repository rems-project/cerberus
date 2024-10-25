#include <cn-executable/utils.h>
#include <signal.h> // for SIGABRT


typedef hash_table ownership_ghost_state;

/* Ownership globals */
ownership_ghost_state* cn_ownership_global_ghost_state;
signed long cn_stack_depth;
struct cn_error_message_info error_msg_info;

static enum cn_logging_level logging_level = CN_LOGGING_INFO;

enum cn_logging_level get_cn_logging_level(void) {
    return logging_level;
}

enum cn_logging_level set_cn_logging_level(enum cn_logging_level new_level) {
    enum cn_logging_level old_level = logging_level;
    logging_level = new_level;
    return old_level;
}

void cn_exit_aux(void) {
    exit(SIGABRT);
}

void static (*cn_exit)(void) = &cn_exit_aux;

void set_cn_exit_cb(void (*callback)(void)) {
    cn_exit = callback;
}

void reset_cn_exit_cb(void) {
    cn_exit = &cn_exit_aux;
}

void print_error_msg_info(void) {
  // cn_printf(CN_LOGGING_INFO, "Function: %s, %s:%d\n", error_msg_info.function_name, error_msg_info.file_name, error_msg_info.line_number);
}

cn_bool *convert_to_cn_bool(_Bool b) {
    cn_bool *res = alloc(sizeof(cn_bool));
    if (!res) exit(1);
    res->val = b;
    return res;
}

_Bool convert_from_cn_bool(cn_bool *b) {
    return b->val;
}

void cn_assert(cn_bool *cn_b) {
    // cn_printf(CN_LOGGING_INFO, "[CN: assertion] function %s, file %s, line %d\n", error_msg_info.function_name, error_msg_info.file_name, error_msg_info.line_number);
    if (!(cn_b->val)) {
        cn_printf(CN_LOGGING_ERROR, "CN assertion failed: function %s, file %s, line %d\n", error_msg_info.function_name, error_msg_info.file_name, error_msg_info.line_number);
        if (error_msg_info.cn_source_loc) {
            cn_printf(CN_LOGGING_ERROR, "CN source location: \n%s\n", error_msg_info.cn_source_loc);
        }
        cn_exit();
    }
}

void c_ghost_assert(cn_bool *cn_b) {
    if (!(cn_b->val)) {
        cn_printf(CN_LOGGING_ERROR, "C memory access failed: function %s, file %s, line %d\n", error_msg_info.function_name, error_msg_info.file_name, error_msg_info.line_number);
        if (error_msg_info.cn_source_loc) {
            cn_printf(CN_LOGGING_ERROR, "CN source location: \n%s\n", error_msg_info.cn_source_loc);
        }
        cn_exit();
    }
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

cn_bool *cn_bool_implies(cn_bool *b1, cn_bool *b2) {
    cn_bool *res = alloc(sizeof(cn_bool));
    res->val = !b1->val || b2->val;
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

void initialise_ownership_ghost_state(void) {
    cn_ownership_global_ghost_state = ht_create();
}

void initialise_ghost_stack_depth(void) {
    cn_stack_depth = 0;
}

void ghost_stack_depth_incr(void) {
    cn_stack_depth++;
    // update_error_message_info(0);
    // print_error_msg_info();
}


#define FMT_PTR "\x1b[33m%#lx\x1b[0m"
// #define KMAG  "\x1B[35m"
#define FMT_PTR_2 "\x1B[35m%#lx\x1B[0m"

void ghost_stack_depth_decr(void) {
    cn_stack_depth--;
    // update_error_message_info(0);
    // print_error_msg_info();
    // leak checking
    hash_table_iterator it = ht_iterator(cn_ownership_global_ghost_state);
    // cn_printf(CN_LOGGING_INFO, "CN pointers leaked at (%ld) stack-depth: ", cn_stack_depth);
    _Bool leaked = false;
    while (ht_next(&it)) {
        intptr_t *key = it.key;
        int *depth = it.value;
        _Bool fine = *depth <= cn_stack_depth;
        if (!fine) {
            leaked = true;
            // cn_printf(CN_LOGGING_INFO, FMT_PTR_2 " (%d),", *key, *depth);
        }
    }
    // cn_printf(CN_LOGGING_INFO, "\n");
    c_ghost_assert(convert_to_cn_bool(!leaked));
}

int ownership_ghost_state_get(signed long *address_key) {
    int *curr_depth_maybe = (int *) ht_get(cn_ownership_global_ghost_state, address_key);
    return curr_depth_maybe ? *curr_depth_maybe : -1;
}

void ownership_ghost_state_set(signed long* address_key, int stack_depth_val) {
    int *new_depth = alloc(sizeof(int));
    *new_depth = stack_depth_val;
    ht_set(cn_ownership_global_ghost_state, address_key, new_depth);
}

void ownership_ghost_state_remove(signed long* address_key) {
    ownership_ghost_state_set(address_key, -1);
}

#define FMT_PTR "\x1b[33m%#lx\x1b[0m"
// #define KMAG  "\x1B[35m"
#define FMT_PTR_2 "\x1B[35m%#lx\x1B[0m"

void dump_ownership_state()
{
  hash_table_iterator it = ht_iterator(cn_ownership_global_ghost_state);
  // cn_printf(CN_LOGGING_INFO, "BEGIN ownership state\n");
  while (ht_next(&it)) {
    int depth = it.value ? *(int*)it.value : -1;
    // cn_printf(CN_LOGGING_INFO, "[%#lx] => depth: %d\n", *it.key, depth);
  }
  // cn_printf(CN_LOGGING_INFO, "END\n");
}


void cn_get_ownership(uintptr_t generic_c_ptr, size_t size) {
    // cn_printf(CN_LOGGING_INFO, "[CN: getting ownership] " FMT_PTR_2 ", size: %lu\n", generic_c_ptr, size);
    //// print_error_msg_info();
    for (int i = 0; i < size; i++) {
        signed long *address_key = alloc(sizeof(long));
        *address_key = generic_c_ptr + i;
        /* // cn_printf(CN_LOGGING_INFO, " off: %d [" FMT_PTR_2 "] (function: %s)\n", i, *address_key, error_msg_info.function_name); */
        int curr_depth = ownership_ghost_state_get(address_key);
        if (curr_depth != cn_stack_depth - 1) {
            cn_printf(CN_LOGGING_ERROR, "CN memory access failed: function %s, file %s, line %d\n", error_msg_info.function_name, error_msg_info.file_name, error_msg_info.line_number);
            cn_printf(CN_LOGGING_ERROR, "  ==> "FMT_PTR"[%d] ("FMT_PTR") -- currently at level: %ld\n", generic_c_ptr, i, (uintptr_t)((char*)generic_c_ptr + i), cn_stack_depth);
            cn_printf(CN_LOGGING_ERROR, "  ==> owned at level : %d\n", curr_depth);
            if (error_msg_info.cn_source_loc) {
                cn_printf(CN_LOGGING_ERROR, "CN source location: \n%s\n", error_msg_info.cn_source_loc);
            }
            //dump_ownership_state();
            cn_exit();
        }
        // cn_assert(convert_to_cn_bool(curr_depth == cn_stack_depth - 1));
        ownership_ghost_state_set(address_key, cn_stack_depth);
    }
}

void cn_put_ownership(uintptr_t generic_c_ptr, size_t size) {
    // cn_printf(CN_LOGGING_INFO, "[CN: returning ownership] " FMT_PTR_2 ", size: %lu\n", generic_c_ptr, size);
    //// print_error_msg_info();
    for (int i = 0; i < size; i++) { 
        signed long *address_key = alloc(sizeof(long));
        *address_key = generic_c_ptr + i;
        int curr_depth = ownership_ghost_state_get(address_key);
        if (curr_depth != cn_stack_depth) {
            cn_printf(CN_LOGGING_ERROR, "CN memory access failed: function %s, file %s, line %d\n", error_msg_info.function_name, error_msg_info.file_name, error_msg_info.line_number);
            cn_printf(CN_LOGGING_ERROR, "  ==> "FMT_PTR"[%d] ("FMT_PTR") -- currently at level: %ld\n", generic_c_ptr, i, (uintptr_t)((char*)generic_c_ptr + i), cn_stack_depth);
            cn_printf(CN_LOGGING_ERROR, "  ==> owned at level: %d\n", curr_depth);
            if (error_msg_info.cn_source_loc) {
                cn_printf(CN_LOGGING_ERROR, "CN source location: \n%s\n", error_msg_info.cn_source_loc);
            }
            //dump_ownership_state();
            cn_exit();
        }
        // cn_assert(convert_to_cn_bool(curr_depth == cn_stack_depth));
        ownership_ghost_state_set(address_key, cn_stack_depth - 1);
    }
}

void cn_assume_ownership(void *generic_c_ptr, unsigned long size, char *fun) {
    // cn_printf(CN_LOGGING_INFO, "[CN: assuming ownership (%s)] " FMT_PTR_2 ", size: %lu\n", fun, (uintptr_t) generic_c_ptr, size);
    //// print_error_msg_info();
    for (int i = 0; i < size; i++) { 
        signed long *address_key = alloc(sizeof(long));
        *address_key = ((uintptr_t) generic_c_ptr) + i;
        /* // cn_printf(CN_LOGGING_INFO, "CN: Assuming ownership for %lu (function: %s)\n",  */
        /*        ((uintptr_t) generic_c_ptr) + i, fun); */
        ownership_ghost_state_set(address_key, cn_stack_depth);
    }
}


void cn_check_ownership(enum OWNERSHIP owned_enum, uintptr_t generic_c_ptr, size_t size) {
  switch (owned_enum)
    {
      case GET:
      {
        cn_get_ownership(generic_c_ptr, size);
        break;
      }
      case PUT:
      {
        cn_put_ownership(generic_c_ptr, size);
        break;
      }
    }
}


void c_add_local_to_ghost_state(uintptr_t ptr_to_local, size_t size) {
  // cn_printf(CN_LOGGING_INFO, "[C access checking] add local:" FMT_PTR ", size: %lu\n", ptr_to_local, size);
  for (int i = 0; i < size; i++) { 
      signed long *address_key = alloc(sizeof(long));
      *address_key = ptr_to_local + i;
      /* // cn_printf(CN_LOGGING_INFO, " off: %d [" FMT_PTR "]\n", i, *address_key); */
      ownership_ghost_state_set(address_key, cn_stack_depth);
  }
}

void c_remove_local_from_ghost_state(uintptr_t ptr_to_local, size_t size) {
  // cn_printf(CN_LOGGING_INFO, "[C access checking] remove local:" FMT_PTR ", size: %lu\n", ptr_to_local, size);
  for (int i = 0; i < size; i++) { 
      signed long *address_key = alloc(sizeof(long));
      *address_key = ptr_to_local + i;
      /* // cn_printf(CN_LOGGING_INFO, " off: %d [" FMT_PTR "]\n", i, *address_key); */
      ownership_ghost_state_remove(address_key);
  }
}

void c_ownership_check(uintptr_t generic_c_ptr, int offset) {
    signed long address_key = 0;
    // cn_printf(CN_LOGGING_INFO, "C: Checking ownership for [ " FMT_PTR " .. " FMT_PTR " ] -- ", generic_c_ptr, generic_c_ptr + offset);
    for (int i = 0; i<offset; i++) {
      address_key = generic_c_ptr + i;
      int curr_depth = ownership_ghost_state_get(&address_key);
      if (curr_depth != cn_stack_depth) {
        cn_printf(CN_LOGGING_ERROR, "C memory access failed: function %s, file %s, line %d\n", error_msg_info.function_name, error_msg_info.file_name, error_msg_info.line_number);
        cn_printf(CN_LOGGING_ERROR, "  ==> "FMT_PTR"[%d] ("FMT_PTR") -- CN stack depth: %ld\n", generic_c_ptr, i, (uintptr_t)((char*)generic_c_ptr + i), cn_stack_depth);
        cn_printf(CN_LOGGING_ERROR, "  ==> retrieved stack depth: %d\n", curr_depth);
        if (error_msg_info.cn_source_loc) {
                cn_printf(CN_LOGGING_ERROR, "CN source location: \n%s\n", error_msg_info.cn_source_loc);
        }
        cn_exit();
      }
    //   c_ghost_assert(convert_to_cn_bool(curr_depth == cn_stack_depth));
    }
    // cn_printf(CN_LOGGING_INFO, "\n");
}

/* TODO: Need address of and size of every stack-allocated variable - could store in struct and pass through. But this is an optimisation */
// void c_map_locals_to_stack_depth(ownership_ghost_state *cn_ownership_global_ghost_state, size_t size, int cn_stack_depth, ...) {
//     va_list args;
 
//     va_start(args, n);
 
//     for (int i = 0; i < n; i++) {
//         uintptr_t fn_local_ptr = va_arg(args, uintptr_t);
//         signed long *address_key = alloc(sizeof(long));
//         *address_key = fn_local_ptr;
//         ghost_state_set(cn_ownership_global_ghost_state, address_key, cn_stack_depth);
//     }
 
//     va_end(args);
// }


cn_map *cn_map_set(cn_map *m, cn_integer *key, void *value) {
    signed long *key_ptr = alloc(sizeof(signed long));
    *key_ptr = key->val;
    ht_set(m, key_ptr, value);
    return m;
}


cn_map *cn_map_deep_copy(cn_map *m1) {
    cn_map *m2 = map_create();

    hash_table_iterator hti = ht_iterator(m1);

    while (ht_next(&hti)) {
        signed long* curr_key = hti.key;
        void *val = ht_get(m1, curr_key);
        ht_set(m2, curr_key, val);
    }

    return m2;
}


cn_map *default_cn_map(void) {
    return map_create();
}

cn_bool *default_cn_bool(void) {
    return convert_to_cn_bool(false);
}

cn_bool *cn_pointer_equality(void *i1, void *i2) {
    return convert_to_cn_bool((((cn_pointer *) i1)->ptr) == (((cn_pointer *) i2)->ptr));
}

cn_bool *cn_pointer_is_null(cn_pointer *p) {
    return convert_to_cn_bool(p->ptr == NULL);
}

cn_bool *cn_pointer_lt(cn_pointer *p1, cn_pointer *p2) {
    return convert_to_cn_bool(p1->ptr < p2->ptr);
}

cn_bool *cn_pointer_le(cn_pointer *p1, cn_pointer *p2) {
    return convert_to_cn_bool(p1->ptr <= p2->ptr);
}

cn_bool *cn_pointer_gt(cn_pointer *p1, cn_pointer *p2) {
    return convert_to_cn_bool(p1->ptr > p2->ptr);
}

cn_bool *cn_pointer_ge(cn_pointer *p1, cn_pointer *p2) {
    return convert_to_cn_bool(p1->ptr >= p2->ptr);
}

cn_pointer *cast_cn_pointer_to_cn_pointer(cn_pointer *p) {\
        return p;
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
            // cn_printf(CN_LOGGING_INFO, "Values not equal!\n");
            return convert_to_cn_bool(0);
        } 
    }

    return convert_to_cn_bool(1);
}

cn_bool *cn_map_equality(cn_map *m1, cn_map *m2, cn_bool *(value_equality_fun)(void *, void *)) {
    return cn_bool_and(cn_map_subset(m1, m2, value_equality_fun), cn_map_subset(m2, m1, value_equality_fun));
}

// TODO (RB) does this need to be in here, or should it be auto-generated?
// See https://github.com/rems-project/cerberus/pull/652 for details
cn_bool *void_pointer_equality(void *p1, void *p2) {
    cn_bool *res = alloc(sizeof(cn_bool));
    res->val = (p1 == p2);
    return res;
}

cn_pointer *convert_to_cn_pointer(void *ptr) {
    cn_pointer *res = (cn_pointer *) alloc(sizeof(cn_pointer));
    res->ptr = ptr; // Carries around an address
    return res;
}

void *convert_from_cn_pointer(cn_pointer *cn_ptr) {
    return cn_ptr->ptr;
}


void update_error_message_info_(const char *function_name, char *file_name, int line_number, char *cn_source_loc) {
    error_msg_info.function_name = function_name;
    error_msg_info.file_name = file_name;
    error_msg_info.line_number = line_number;
    error_msg_info.cn_source_loc = cn_source_loc;
    //// print_error_msg_info();
}

void initialise_error_msg_info_(const char *function_name, char *file_name, int line_number) {
  // cn_printf(CN_LOGGING_INFO, "Initialising error message info\n");
  error_msg_info.function_name = function_name;
  error_msg_info.file_name = file_name;
  error_msg_info.line_number = line_number;
  error_msg_info.cn_source_loc = 0;
}


static uint32_t cn_fls(uint32_t x)
{
    return x ? sizeof(x) * 8 - __builtin_clz(x) : 0;
}

static uint64_t cn_flsl(uint64_t x)
{
    return x ? sizeof(x) * 8 - __builtin_clzl(x) : 0;
}


cn_bits_u32 *cn_bits_u32_fls(cn_bits_u32 *i1) {
        cn_bits_u32 *res = (cn_bits_u32 *) alloc(sizeof(cn_bits_u32));
        res->val = cn_fls(i1->val);
        return res;
    }

cn_bits_u64 *cn_bits_u64_flsl(cn_bits_u64 *i1) {
        cn_bits_u64 *res = (cn_bits_u64 *) alloc(sizeof(cn_bits_u64));
        res->val = cn_flsl(i1->val);
        return res;
    }


void *cn_aligned_alloc(size_t align, size_t size) 
{
  void *p = aligned_alloc(align, size);
  char str[] = "cn_aligned_malloc";
  if (p) {
    cn_assume_ownership((void*) p, size, str);
    return p;
  } else {
    cn_printf(CN_LOGGING_INFO, "aligned_alloc failed\n");
    return p;
  }
}

void *cn_malloc(unsigned long size) 
{
  void *p = malloc(size);
  char str[] = "cn_malloc";
  if (p) {
    cn_assume_ownership((void*) p, size, str);
    return p;
  } else {
    cn_printf(CN_LOGGING_INFO, "malloc failed\n");
    return p;
  }
}

void *cn_calloc(size_t num, size_t size) 
{
  void *p = calloc(num, size);
  char str[] = "cn_calloc";
  if (p) {
    cn_assume_ownership((void*) p, num*size, str);
    return p;
  } else {
    cn_printf(CN_LOGGING_INFO, "calloc failed\n");
    return p;
  }
}

void cn_free_sized(void* malloced_ptr, size_t size)
{
  // cn_printf(CN_LOGGING_INFO, "[CN: freeing ownership] " FMT_PTR ", size: %lu\n", (uintptr_t) malloced_ptr, size);
  for (int i = 0; i < size; i++) {
      signed long *address_key = alloc(sizeof(long));
      *address_key = (uintptr_t) malloced_ptr + i;
      /* printf(" off: %d [" FMT_PTR "]\n", i, *address_key); */
      int curr_depth = ownership_ghost_state_get(address_key);
      c_ghost_assert(convert_to_cn_bool(curr_depth == cn_stack_depth));
      ownership_ghost_state_remove(address_key);
  }
}

void cn_print_u64(const char *str, unsigned long u)
{
  // cn_printf(CN_LOGGING_INFO, "\n\nprint %s: %20lx,  %20lu\n\n", str, u, u);
}

void cn_print_nr_u64(int i, unsigned long u)
{
  // cn_printf(CN_LOGGING_INFO, "\n\nprint %d: %20lx,  %20lu\n", i, u, u);
}

