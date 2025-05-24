#ifndef	_SETJMP_H_
#define	_SETJMP_H_

/* TODO: this type is required to be an array type, but with no requirement on
 * the element type or size. It would be better have some richer builtin
 * mechanism keeping these opaque.
 * Making an arbitrary choice for now (from macOS arm64)
 */
typedef int jmp_buf[48];

int setjmp(jmp_buf env);
_Noreturn void longjmp(jmp_buf env, int val);

#if defined(__cerb__) && !defined(__cerb_syntax_only__)
#error <setjmp.h> is not currently supported by Cerberus
#endif

#else
#endif
