// This creates a ton of models, and previously 
// caused so many solvers to be created that macOS
// runs out of file descriptors with the default 256 limit. 
// This test should produce verification errors without crashing CN.

typedef long long int64_t;

typedef unsigned char uint8_t;

typedef unsigned short uint16_t;

typedef unsigned int uint32_t;
typedef unsigned long long uint64_t;
typedef char __darwin_uuid_string_t;
struct __darwin_pthread_handler_rec {
  char __opaque[8];
};
struct _opaque_pthread_once_t {
  long __sig;
  char __opaque[8][192];
};
struct _opaque_pthread_rwlockattr_t {
  struct __darwin_pthread_handler_rec *__cleanup_stack;
};
typedef unsigned long uintptr_t;

static uint8_t f_22() {
  return 4;
  3;
  0;
  1;
  2;
  3;
  0;
}

static uint8_t f_32() {
  uint8_t d_33[3];
  uint8_t d_34[3];
}

int f_37();

struct s_39 {
  uint8_t d_40[2];
  uint8_t d_41[2];
};
int f_43(struct s_39 *a);

uint32_t sensors[2][2];
uint8_t d_46[4];
extern uint8_t d_47[2][2];
extern uint8_t d_48[2][2];
extern uint8_t d_49[2][2][2];
int d_50;

typedef int size_t;
uint16_t _OSSwapInt16(_data) {}
uint32_t _OSSwapInt32(_data) { _data = __builtin_bswap32(_data); }
struct {
  uint64_t __val;
} __attribute__();
uint16_t OSReadSwapInt16(_offset) {}
uint32_t OSReadSwapInt32() {}
uint64_t OSReadSwapInt64() {}
void f_61(_data){}
int f_62(FILE);

int fflush0;
typedef struct {
  int64_t tv_sec;
};
typedef int clockid_t;
int f_69(clockid_t, struct timespec *);

int f_71(void);

void f_73() {
  for (int i = 0; i < 4;)
    for (int c = 0; c < 2; ++c) {
      for (int s = 0; s < 2; ++s) {
        switch (d_47[c][s]) {
        case 0:
        case 1:
          d_49[c][s][0] = 1;
        case 3:
          d_48[c][s] = 1;
        case 4:
        case 5:
          (__builtin_expect(!("" && 0), ) ? (void)0
                                                                  : (void)0);
        }
      }
    }
}
void *f_91(void *arg) {
  while (1)
    ;
}
int;

int d_97;

int f_99(res);

int f_101(res);

uint32_t f_103() {
  while (1)
    ;
}