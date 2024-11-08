#ifndef CN_GEN_BACKTRACK_H
#define CN_GEN_BACKTRACK_H

#include <stdlib.h>
#include <stdint.h>

uint16_t cn_gen_backtrack_depth();
uint16_t cn_gen_backtrack_max_depth();
void cn_gen_backtrack_set_max_depth(uint16_t msd);
void cn_gen_backtrack_increment_depth();
void cn_gen_backtrack_decrement_depth();

enum cn_gen_backtrack_request {
    CN_GEN_BACKTRACK_NONE,
    CN_GEN_BACKTRACK_ASSERT,
    CN_GEN_BACKTRACK_ALLOC,
    CN_GEN_BACKTRACK_DEPTH
};

enum cn_gen_backtrack_request cn_gen_backtrack_type(void);

void cn_gen_backtrack_reset(void);

void cn_gen_backtrack_assert_failure(void);

void cn_gen_backtrack_relevant_add(char* varname);

void cn_gen_backtrack_relevant_add_many(char* toAdd[]);

int cn_gen_backtrack_relevant_contains(char* varname);

void cn_gen_backtrack_depth_exceeded();

/**
 * @brief Remaps a relevant variable
 *
 * @param from A NULL-terminated variable name
 * @param to A NULL-terminated variable name to replace `from` with
 * @return int Was the remapping successful?
 */
int cn_gen_backtrack_relevant_remap(char* from, char* to);

/**
 * @brief Remaps multiple relevant variables
 *
 * @param from A NULL-terminated list of `char*`
 * @param to A NULL-terminated list of `char*` of the same length as `from`
 * @return int How many remappings were successful?
 */
int cn_gen_backtrack_relevant_remap_many(char* from[], char* to[]);

void cn_gen_backtrack_alloc_set(size_t sz);

size_t cn_gen_backtrack_alloc_get();

#endif // CN_GEN_BACKTRACK_H
