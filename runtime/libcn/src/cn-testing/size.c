#include <cn-testing/size.h>

static size_t global_size = 20;

size_t cn_gen_get_size(void) {
    return global_size;
}

void cn_gen_set_size(size_t sz) {
    global_size = sz;
}

static size_t global_max_size = 25;

size_t cn_gen_get_max_size(void) {
    return global_max_size;
}

void cn_gen_set_max_size(size_t sz) {
    global_max_size = sz;
}

static uint16_t stack_depth = 0;
static uint16_t max_stack_depth = UINT8_MAX;

uint16_t cn_gen_depth() {
    return stack_depth;
}

uint16_t cn_gen_max_depth() {
    return max_stack_depth;
}

void cn_gen_set_max_depth(uint16_t msd) {
    max_stack_depth = msd;
}

void cn_gen_increment_depth() {
    stack_depth++;
}

void cn_gen_decrement_depth() {
    stack_depth--;
}

static uint16_t depth_failures_allowed = UINT16_MAX;

void cn_gen_set_depth_failures_allowed(uint16_t allowed) {
    depth_failures_allowed = allowed;
}

uint16_t cn_gen_get_depth_failures_allowed() {
    return depth_failures_allowed;
}

static uint16_t size_split_backtracks_allowed = 0;

void cn_gen_set_size_split_backtracks_allowed(uint16_t allowed) {
    size_split_backtracks_allowed = allowed;
}

uint16_t cn_gen_get_size_split_backtracks_allowed() {
    return size_split_backtracks_allowed;
}
