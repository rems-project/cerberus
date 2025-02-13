#include <stdint.h>
#include <stdlib.h>

size_t cn_gen_get_size(void);
void cn_gen_set_size(size_t sz);

size_t cn_gen_get_max_size(void);
void cn_gen_set_max_size(size_t sz);

uint16_t cn_gen_depth();
uint16_t cn_gen_max_depth();
void cn_gen_set_max_depth(uint16_t msd);
void cn_gen_increment_depth();
void cn_gen_decrement_depth();

void cn_gen_set_depth_failures_allowed(uint16_t allowed);
uint16_t cn_gen_get_depth_failures_allowed();

void cn_gen_set_size_split_backtracks_allowed(uint16_t allowed);
uint16_t cn_gen_get_size_split_backtracks_allowed();

void cn_gen_set_input_timeout(uint8_t seconds);
uint8_t cn_gen_get_input_timeout(void);

void cn_gen_set_input_timer(uint64_t time);
uint64_t cn_gen_get_input_timer(void);

uint64_t cn_gen_get_milliseconds(void);
