#include<string.h>
#include<stdint.h>

// Let's assume that p[0] = a pointer to one byte past block l
int *f(int *p[1]) {
    unsigned char buf[sizeof(int*)];
    intptr_t q[1];
    memcpy(buf, &p[0], sizeof(int*)); // bytes of buf[0..7] reserves provenance of l
    memcpy(q, buf, sizeof(int*)); // bytes of q reserves provenance of l

    intptr_t i = q[0]; // i does not have any provenance
                       // because it's a pure integer
                       // (In OOPSLA'18, i is a 'poison' value
                       //  (which is a value representing errorneous
                       //   state))
    q[0] = i; // Now q[0] does not have any provenance
    // Wants to remove load+store pair above, because they do nothing..?

    memcpy(buf, q, sizeof(int*));     // buf does not have any byte having provenance
    memcpy(&p[0], buf, sizeof(int*)); // value of p[0] does have provenance

    int *retval = p[0]; // retval regains provenance, but what if
                        // p[0] was originally a pointer to one byte past
                        // block l?
    return retval; // Can this be optimized to `p[0]`?
}
int main() {
  int i=5;
  int j=6;
  int *p[1] = { &i + 1 };
  f(p);
}
