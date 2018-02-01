int f(int); // this has external linkage
static int f(int); // but this has internal linkage, UB (§6.2.2#7)
