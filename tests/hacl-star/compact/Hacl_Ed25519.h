/* This file was generated by KreMLin <https://github.com/FStarLang/kremlin>
 * KreMLin invocation: /home/jonathan/Code/everest/kremlin/krml -I /home/jonathan/Code/everest/hacl-star/code/lib/kremlin -I /home/jonathan/Code/everest/kremlin/kremlib/compat -I /home/jonathan/Code/everest/hacl-star/specs -I /home/jonathan/Code/everest/hacl-star/specs/old -I . -ccopt -march=native -verbose -ldopt -flto -tmpdir ed25519-c -I ../bignum -I ../curve25519 -I ../hash -bundle Hacl.Ed25519=* -minimal -add-include "kremlib.h" -skip-compilation ed25519-c/out.krml -o ed25519-c/Hacl_Ed25519.c
 * F* version: 8f0ddba4
 * KreMLin version: 9768dccd
 */


#ifndef __Hacl_Ed25519_H
#define __Hacl_Ed25519_H


#include "kremlib.h"

typedef uint8_t *Hacl_Ed25519_uint8_p;

typedef uint8_t *Hacl_Ed25519_hint8_p;

void Hacl_Ed25519_sign(uint8_t *signature, uint8_t *secret, uint8_t *msg, uint32_t len1);

bool Hacl_Ed25519_verify(uint8_t *output, uint8_t *msg, uint32_t len1, uint8_t *signature);

void Hacl_Ed25519_secret_to_public(uint8_t *output, uint8_t *secret);

void Hacl_Ed25519_expand_keys(uint8_t *ks, uint8_t *secret);

void Hacl_Ed25519_sign_expanded(uint8_t *signature, uint8_t *ks, uint8_t *msg, uint32_t len1);

#define __Hacl_Ed25519_H_DEFINED
#endif
