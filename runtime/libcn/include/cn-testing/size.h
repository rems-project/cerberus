#include <stdlib.h>
#include <stdint.h>

size_t cn_gen_get_size(void);
void cn_gen_set_size(size_t sz);

size_t cn_gen_get_max_size(void);
void cn_gen_set_max_size(size_t sz);

uint16_t cn_gen_depth();
uint16_t cn_gen_max_depth();
void cn_gen_set_max_depth(uint16_t msd);
void cn_gen_increment_depth();
void cn_gen_decrement_depth();
