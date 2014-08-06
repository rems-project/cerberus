typedef __cerbty_jmp_buf jmp_buf;

int setjmp(jmp_buf env);
_Noreturn void longjmp(jmp_buf env, int val);
