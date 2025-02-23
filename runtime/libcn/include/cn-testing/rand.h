#ifndef CN_GEN_RAND_H
#define CN_GEN_RAND_H

#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

void cn_gen_srand(uint64_t seed);
uint64_t cn_gen_rand(void);

uint8_t cn_gen_uniform_u8(uint8_t);
uint16_t cn_gen_uniform_u16(uint16_t);
uint32_t cn_gen_uniform_u32(uint32_t);
uint64_t cn_gen_uniform_u64(uint64_t);

int8_t cn_gen_uniform_i8(uint8_t);
int16_t cn_gen_uniform_i16(uint16_t);
int32_t cn_gen_uniform_i32(uint32_t);
int64_t cn_gen_uniform_i64(uint64_t);

uint8_t cn_gen_range_u8(uint8_t, uint8_t);
uint16_t cn_gen_range_u16(uint16_t, uint16_t);
uint32_t cn_gen_range_u32(uint32_t, uint32_t);
uint64_t cn_gen_range_u64(uint64_t, uint64_t);

int8_t cn_gen_range_i8(int8_t, int8_t);
int16_t cn_gen_range_i16(int16_t, int16_t);
int32_t cn_gen_range_i32(int32_t, int32_t);
int64_t cn_gen_range_i64(int64_t, int64_t);

uint8_t cn_gen_lt_u8(uint8_t);
uint16_t cn_gen_lt_u16(uint16_t);
uint32_t cn_gen_lt_u32(uint32_t);
uint64_t cn_gen_lt_u64(uint64_t);

int8_t cn_gen_lt_i8(int8_t);
int16_t cn_gen_lt_i16(int16_t);
int32_t cn_gen_lt_i32(int32_t);
int64_t cn_gen_lt_i64(int64_t);

uint8_t cn_gen_ge_u8(uint8_t);
uint16_t cn_gen_ge_u16(uint16_t);
uint32_t cn_gen_ge_u32(uint32_t);
uint64_t cn_gen_ge_u64(uint64_t);

int8_t cn_gen_ge_i8(int8_t);
int16_t cn_gen_ge_i16(int16_t);
int32_t cn_gen_ge_i32(int32_t);
int64_t cn_gen_ge_i64(int64_t);

uint8_t cn_gen_mult_range_u8(uint8_t, uint8_t, uint8_t);
uint16_t cn_gen_mult_range_u16(uint16_t, uint16_t, uint16_t);
uint32_t cn_gen_mult_range_u32(uint32_t, uint32_t, uint32_t);
uint64_t cn_gen_mult_range_u64(uint64_t, uint64_t, uint64_t);

int8_t cn_gen_mult_range_i8(int8_t, int8_t, int8_t);
int16_t cn_gen_mult_range_i16(int16_t, int16_t, int16_t);
int32_t cn_gen_mult_range_i32(int32_t, int32_t, int32_t);
int64_t cn_gen_mult_range_i64(int64_t, int64_t, int64_t);

uint8_t cn_gen_mult_u8(uint8_t);
uint16_t cn_gen_mult_u16(uint16_t);
uint32_t cn_gen_mult_u32(uint32_t);
uint64_t cn_gen_mult_u64(uint64_t);

int8_t cn_gen_mult_i8(int8_t);
int16_t cn_gen_mult_i16(int16_t);
int32_t cn_gen_mult_i32(int32_t);
int64_t cn_gen_mult_i64(int64_t);

void cn_gen_shuffle(void* arr, size_t len, size_t size);

void cn_gen_split(size_t n, size_t* arr[], size_t len);

uint64_t cn_gen_rand_retry(void);

typedef void* cn_gen_rand_checkpoint;

cn_gen_rand_checkpoint cn_gen_rand_save(void);

void cn_gen_rand_restore(cn_gen_rand_checkpoint checkpoint);

void cn_gen_rand_replace(cn_gen_rand_checkpoint checkpoint);

#ifdef __cplusplus
}
#endif

#endif  // CN_GEN_RAND_H
