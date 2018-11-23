#define __attribute__(a)
# 1 "ecu_table.c"
# 1 "/home/patrick/src/e7/prex/usr/e7/lib//"
# 1 "<built-in>"
# 1 "<command-line>"
# 1 "ecu_table.c"
# 1 "../include/ecu/table.h" 1


# 1 "../include/ecu/types.h" 1
# 14 "../include/ecu/types.h"
# 1 "/home/patrick/src/e7/prex/include/machine/types.h" 1






# 1 "/home/patrick/src/e7/prex/include/ppc/types.h" 1
# 10 "/home/patrick/src/e7/prex/include/ppc/types.h"
# 1 "/home/patrick/src/e7/prex/include/sys/cdefs.h" 1
# 11 "/home/patrick/src/e7/prex/include/ppc/types.h" 2





typedef signed char int8_t;
typedef unsigned char uint8_t;
typedef short int16_t;
typedef unsigned short uint16_t;
typedef int int32_t;
typedef unsigned int uint32_t;
typedef long long int64_t;
typedef unsigned long long uint64_t;

typedef uint8_t u8;
typedef uint16_t u16;
typedef uint32_t u32;
typedef uint64_t u64;
typedef int8_t s8;
typedef int16_t s16;
typedef int32_t s32;
typedef int64_t s64;
typedef float f32;
typedef volatile u8 vu8;
typedef volatile s16 vs16;
typedef volatile u16 vu16;
typedef volatile s32 vs32;
typedef volatile u32 vu32;

typedef union {
 s32 as_s32;
 u32 as_u32;
 f32 as_f32;
 void *as_pv;
} arg_t __attribute__ ((__transparent_union__));


typedef struct {
 int rc;
 arg_t rval;
} ret64_t;

typedef struct {
 int rc;
 f32 rval;
} rcf32;
# 8 "/home/patrick/src/e7/prex/include/machine/types.h" 2
# 15 "../include/ecu/types.h" 2



typedef char bool;
# 113 "../include/ecu/types.h"
typedef void (*initcall_t)(void);
typedef void (*exitcall_t)(void);
# 4 "../include/ecu/table.h" 2
# 40 "../include/ecu/table.h"
enum axis_f32_cfg_clamp {
 CLAMP_MIN_OFF = 0x02, CLAMP_MIN_ON = 0x01, CLAMP_MIN_MASK = 0x03,
 CLAMP_MAX_OFF = 0x08, CLAMP_MAX_ON = 0x04, CLAMP_MAX_MASK = 0x0C,
};

typedef const struct {
 const u32 clamp;
 const u32 num;
 f32 volatile const *const data;
} axis_f32_cfg;

typedef struct {
 u32 index;
} axis_f32_state;







typedef const struct {
 axis_f32_cfg x;
 f32 volatile const *const data;
} interp_2d_f32_cfg;

typedef struct {
 axis_f32_state x;
} interp_2d_f32_state;
# 79 "../include/ecu/table.h"
extern f32 interp_2d_f32(interp_2d_f32_state *state,
    interp_2d_f32_cfg *cfg, f32 x);

extern void interp_2d_f32_init(interp_2d_f32_state *state,
          interp_2d_f32_cfg *cfg, f32 x);
# 105 "../include/ecu/table.h"
typedef const struct {
 axis_f32_cfg x, y;
 f32 volatile const *const data;
} interp_3d_f32_cfg;

typedef struct {
 axis_f32_state x, y;
} interp_3d_f32_state;
# 124 "../include/ecu/table.h"
extern f32 interp_3d_f32(interp_3d_f32_state *state,
    interp_3d_f32_cfg *cfg, f32 x, f32 y);

extern void interp_3d_f32_init(interp_3d_f32_state *state,
          interp_3d_f32_cfg *cfg, f32 x, f32 y);
# 152 "../include/ecu/table.h"
typedef const struct {
 axis_f32_cfg x, y, z;
 f32 volatile const *const data;
} interp_4d_f32_cfg;

typedef struct {
 axis_f32_state x, y, z;
} interp_4d_f32_state;
# 172 "../include/ecu/table.h"
extern f32 interp_4d_f32(interp_4d_f32_state *state, interp_4d_f32_cfg *cfg,
    f32 x, f32 y, f32 z);

extern void interp_4d_f32_init(interp_4d_f32_state *state, interp_4d_f32_cfg *cfg,
          f32 x, f32 y, f32 z);
# 2 "ecu_table.c" 2
# 1 "/home/patrick/src/e7/prex/include/prex/prex.h" 1
# 34 "/home/patrick/src/e7/prex/include/prex/prex.h"
# 1 "/home/patrick/src/e7/prex/conf/config.h" 1
# 35 "/home/patrick/src/e7/prex/include/prex/prex.h" 2


# 1 "/home/patrick/src/e7/prex/include/sys/types.h" 1
# 41 "/home/patrick/src/e7/prex/include/sys/types.h"
# 1 "/home/patrick/src/e7/prex/include/machine/ansi.h" 1






# 1 "/home/patrick/src/e7/prex/include/ppc/ansi.h" 1
# 8 "/home/patrick/src/e7/prex/include/machine/ansi.h" 2
# 42 "/home/patrick/src/e7/prex/include/sys/types.h" 2
# 1 "/home/patrick/src/e7/prex/include/machine/types.h" 1
# 43 "/home/patrick/src/e7/prex/include/sys/types.h" 2
# 1 "/home/patrick/src/e7/prex/include/prex/types.h" 1
# 34 "/home/patrick/src/e7/prex/include/prex/types.h"
# 1 "/home/patrick/src/e7/prex/include/machine/types.h" 1
# 35 "/home/patrick/src/e7/prex/include/prex/types.h" 2

typedef unsigned long object_t;
typedef unsigned long task_t;
typedef unsigned long thread_t;
typedef unsigned long device_t;
typedef unsigned long mutex_t;
typedef unsigned long cond_t;
typedef unsigned long sem_t;
typedef uint32_t cap_t;
# 44 "/home/patrick/src/e7/prex/include/sys/types.h" 2
# 1 "/home/patrick/src/e7/prex/include/prex/pthreadtypes.h" 1






typedef struct pthread_attr {
 int sched_priority;
 int sched_policy;
 int detached;
 unsigned long stacksize;
 unsigned long magic;
 char name[12];
 const void *key;
} pthread_attr_t;





typedef unsigned long pthread_key_t;
# 30 "/home/patrick/src/e7/prex/include/prex/pthreadtypes.h"
struct pthread_info;
typedef struct pthread_info* pthread_t;
# 45 "/home/patrick/src/e7/prex/include/sys/types.h" 2

typedef unsigned char u_char;
typedef unsigned short u_short;
typedef unsigned int u_int;
typedef unsigned long u_long;
typedef unsigned short ushort;
typedef unsigned int uint;

typedef uint32_t dev_t;
typedef uint32_t gid_t;
typedef uint32_t ino_t;
typedef uint16_t mode_t;
typedef uint16_t nlink_t;
typedef int32_t off_t;
typedef int32_t pid_t;
typedef uint32_t uid_t;
typedef unsigned long rlim_t;

# 1 "/home/patrick/src/e7/prex/include/sys/endian.h" 1
# 49 "/home/patrick/src/e7/prex/include/sys/endian.h"
# 1 "/home/patrick/src/e7/prex/conf/config.h" 1
# 50 "/home/patrick/src/e7/prex/include/sys/endian.h" 2

# 1 "/home/patrick/src/e7/prex/include/sys/types.h" 1
# 52 "/home/patrick/src/e7/prex/include/sys/endian.h" 2








uint32_t htonl(uint32_t);
uint16_t htons(uint16_t);
uint32_t ntohl(uint32_t);
uint16_t ntohs(uint16_t);

# 64 "/home/patrick/src/e7/prex/include/sys/types.h" 2


typedef unsigned long clock_t;




typedef unsigned int size_t;




typedef int ssize_t;




typedef long time_t;
# 98 "/home/patrick/src/e7/prex/include/sys/types.h"
typedef int32_t fd_mask;






typedef struct fd_set {
 fd_mask fds_bits[(((16) + (((sizeof(fd_mask) * 8)) - 1)) / ((sizeof(fd_mask) * 8)))];
} fd_set;
# 38 "/home/patrick/src/e7/prex/include/prex/prex.h" 2
# 1 "/home/patrick/src/e7/prex/include/sys/param.h" 1
# 37 "/home/patrick/src/e7/prex/include/sys/param.h"
# 1 "/home/patrick/src/e7/prex/conf/config.h" 1
# 38 "/home/patrick/src/e7/prex/include/sys/param.h" 2





# 1 "/home/patrick/src/e7/prex/include/sys/null.h" 1
# 44 "/home/patrick/src/e7/prex/include/sys/param.h" 2
# 56 "/home/patrick/src/e7/prex/include/sys/param.h"
# 1 "/home/patrick/src/e7/prex/include/sys/syslimits.h" 1
# 31 "/home/patrick/src/e7/prex/include/sys/syslimits.h"
# 1 "/home/patrick/src/e7/prex/conf/config.h" 1
# 32 "/home/patrick/src/e7/prex/include/sys/syslimits.h" 2
# 57 "/home/patrick/src/e7/prex/include/sys/param.h" 2
# 87 "/home/patrick/src/e7/prex/include/sys/param.h"
# 1 "/home/patrick/src/e7/prex/include/sys/signal.h" 1
# 42 "/home/patrick/src/e7/prex/include/sys/signal.h"
# 1 "/home/patrick/src/e7/prex/include/machine/signal.h" 1






# 1 "/home/patrick/src/e7/prex/include/ppc/signal.h" 1
# 11 "/home/patrick/src/e7/prex/include/ppc/signal.h"
typedef int sig_atomic_t;
# 20 "/home/patrick/src/e7/prex/include/ppc/signal.h"
struct sigcontext;
# 8 "/home/patrick/src/e7/prex/include/machine/signal.h" 2
# 43 "/home/patrick/src/e7/prex/include/sys/signal.h" 2
# 87 "/home/patrick/src/e7/prex/include/sys/signal.h"
typedef unsigned int sigset_t;

union sigval {
 int sival_int;
 void *sival_ptr;
};

struct siginfo {
 int si_signo;
 int si_code;
 union sigval si_value;
};

typedef struct siginfo siginfo_t;




struct sigaction {
 union {
  void (*__sa_handler) (int);
  void (*__sa_sigaction) (int, siginfo_t *, void *);
 } __sigaction_u;
 sigset_t sa_mask;
 int sa_flags;
};
# 134 "/home/patrick/src/e7/prex/include/sys/signal.h"
typedef void (*sig_t)(int);




struct sigaltstack {
 char *ss_base;
 int ss_size;
 int ss_flags;
};







struct sigvec {
 void (*sv_handler)(int);
 int sv_mask;
 int sv_flags;
};
# 164 "/home/patrick/src/e7/prex/include/sys/signal.h"
struct sigstack {
 char *ss_sp;
 int ss_onstack;
};
# 181 "/home/patrick/src/e7/prex/include/sys/signal.h"

void (*signal(int, void (*)(int)))(int);

# 88 "/home/patrick/src/e7/prex/include/sys/param.h" 2


# 1 "/home/patrick/src/e7/prex/include/machine/limits.h" 1






# 1 "/home/patrick/src/e7/prex/include/ppc/limits.h" 1
# 8 "/home/patrick/src/e7/prex/include/machine/limits.h" 2
# 91 "/home/patrick/src/e7/prex/include/sys/param.h" 2
# 39 "/home/patrick/src/e7/prex/include/prex/prex.h" 2
# 1 "/home/patrick/src/e7/prex/include/prex/sysinfo.h" 1
# 44 "/home/patrick/src/e7/prex/include/prex/sysinfo.h"
struct info_kernel {
 char sysname[12];
 char version[12];
 char blddate[12];
 char machine[12];
 char hostname[12];
};




struct info_memory {
 size_t total;
 size_t free;
 size_t kpage_total;
 size_t kpage_free;
 size_t kernel;
};




struct info_thread {
 u_long cookie;
 int state;
 int policy;
 int prio;
 int base_prio;
 int suspend_count;
 u_int total_ticks;
 thread_t id;
 task_t task;
 char th_name[12];
 char task_name[12];
 char sleep_event[12];
};
# 92 "/home/patrick/src/e7/prex/include/prex/sysinfo.h"
struct info_device {
 u_long cookie;
 device_t id;
 int flags;
 char name[12];
};
# 110 "/home/patrick/src/e7/prex/include/prex/sysinfo.h"
struct info_timer {
 int hz;
};
# 40 "/home/patrick/src/e7/prex/include/prex/prex.h" 2
# 107 "/home/patrick/src/e7/prex/include/prex/prex.h"

int object_create(const char *name, object_t *obj);
int object_destroy(object_t obj);
int object_lookup(const char *name, object_t *obj);

int msg_send(object_t obj, void *msg, size_t size, u_long timeout);
int msg_receive(object_t obj, void *msg, size_t size, u_long timeout);
int msg_reply(object_t obj, void *msg, size_t size);

int vm_allocate(task_t task, void **addr, size_t size, int anywhere);
int vm_free(task_t task, void *addr);
int vm_attribute(task_t task, void *addr, int attr);
int vm_map(task_t target, void *addr, size_t size, void **alloc);

int task_create(task_t parent, int vm_option, task_t *child);
int task_terminate(task_t task);
task_t task_self(void);
int task_suspend(task_t task);
int task_resume(task_t task);
int task_name(task_t task, const char *name);
int task_getcap(task_t task, cap_t *cap);
int task_setcap(task_t task, cap_t *cap);

int thread_create(task_t task, thread_t *th);
int thread_terminate(thread_t th);
int thread_load(thread_t th, void (*entry)(void), void *stack);
thread_t thread_self(void);
void thread_yield(void);
int thread_suspend(thread_t th);
int thread_resume(thread_t th);
int thread_name(thread_t th, const char *name);
int thread_getprio(thread_t th, int *prio);
int thread_setprio(thread_t th, int prio);
int thread_getpolicy(thread_t th, int *policy);
int thread_setpolicy(thread_t th, int policy);

int timer_sleep(u_long delay, u_long *remain);
int timer_alarm(u_long delay, u_long *remain);
int timer_periodic(thread_t th, u_long start, u_long period);
int timer_waitperiod(void);

int exception_setup(void (*handler)(int, void *));
int exception_return(void *regs);
int exception_raise(task_t task, int excpt);
int exception_wait(int *excpt);

int device_open(const char *name, int mode, device_t *dev);
int device_close(device_t dev);
int device_read(device_t dev, void *buf, size_t *nbyte, int blkno);
int device_write(device_t dev, void *buf, size_t *nbyte, int blkno);
int device_ioctl(device_t dev, int cmd, u_long arg);

int mutex_init(mutex_t *mu);
int mutex_destroy(mutex_t *mu);
int mutex_trylock(mutex_t *mu);
int mutex_lock(mutex_t *mu);
int mutex_unlock(mutex_t *mu);

int cond_init(cond_t *cond);
int cond_destroy(cond_t *cond);
int cond_wait(cond_t *cond, mutex_t *mu, u_long timeout);
int cond_signal(cond_t *cond);
int cond_broadcast(cond_t *cond);

int sem_init(sem_t *sem, u_int value);
int sem_destroy(sem_t *sem);
int sem_wait(sem_t *sem, u_long timeout);
int sem_trywait(sem_t *sem);
int sem_post(sem_t *sem);
int sem_getvalue(sem_t *sem, u_int *value);

int sys_info(int type, void *buf);
int sys_log(const char *);
void sys_panic(const char *) __attribute__((noreturn));
int sys_time(u_long *ticks);
int sys_debug(int cmd, ...);



void panic(const char *, ...);




# 3 "ecu_table.c" 2
# 1 "../include/ecu/verbose.h" 1

# 1 "/home/patrick/src/e7/prex/include/verbose.h" 1
# 14 "/home/patrick/src/e7/prex/include/verbose.h"
# 1 "/home/patrick/src/e7/prex/include/sys/syslog.h" 1
# 172 "/home/patrick/src/e7/prex/include/sys/syslog.h"
# 1 "/home/patrick/src/e7/prex/include/machine/ansi.h" 1
# 173 "/home/patrick/src/e7/prex/include/sys/syslog.h" 2



void closelog(void);
void openlog(const char *, int, int);
int setlogmask(int);

void syslog(int, const char *, ...);
void vsyslog(int, const char *, __builtin_va_list);





# 15 "/home/patrick/src/e7/prex/include/verbose.h" 2

# 1 "/home/patrick/src/e7/prex/include/ppc/mpc5500/spr.h" 1
# 21 "/home/patrick/src/e7/prex/include/ppc/mpc5500/spr.h"
# 1 "/home/patrick/src/e7/prex/include/ppc/bit.h" 1
# 22 "/home/patrick/src/e7/prex/include/ppc/mpc5500/spr.h" 2
# 1 "/home/patrick/src/e7/prex/conf/config.h" 1
# 23 "/home/patrick/src/e7/prex/include/ppc/mpc5500/spr.h" 2
# 17 "/home/patrick/src/e7/prex/include/verbose.h" 2
# 91 "/home/patrick/src/e7/prex/include/verbose.h"
enum VERBOSE_FLAGS
{


        VB_ALL = 0x7fffffff , VB_NONE = 0x00000000 , VB_CRIT = 0x00000001 , VB_INFO = 0x00000002 , VB_DEBUG = 0x00000004 , VB_MORE = 0x00000008 , VB_CAN = 0x00000100 , VB_ETH = 0x00000200 , VB_XCP = 0x00000400 , VB_OUT = 0x00000800 , VB_ADC = 0x00001000 , VB_DMA = 0x00002000 , VB_CORE = 0x00004000 , VB_MEM = 0x00008000 , VB_RELOC = 0x00010000 , VB_LOGGING = 0x00020000 , VB_STREAM = 0x00040000 , VB_INIT = 0x00080000 , VB_SECURITY = 0x00100000 , VB_PTHREAD = 0x00200000 ,
};

static inline uint32_t verbose_get(void)
{
 return ({ u32 rval; asm volatile("mfspr %0," "256" : "=r" (rval)); rval; });
}

static inline void verbose_set(uint32_t val)
{
 asm volatile("mtspr " "256" ",%0" : : "r" (val));
}
# 3 "../include/ecu/verbose.h" 2
# 4 "ecu_table.c" 2
# 1 "/home/patrick/src/e7/prex/usr/include/assert.h" 1
# 59 "/home/patrick/src/e7/prex/usr/include/assert.h"

void __assert(const char *, int, const char *);

# 5 "ecu_table.c" 2


struct axis_current {
 s32 index;
 f32 percent;
};



static struct axis_current find_index_f32(axis_f32_state *state,
           axis_f32_cfg *cfg, f32 val)
{
 const f32 *data = (f32 *)cfg->data;
 int rem = cfg->num - 2;




 int prev = state->index;
 u32 offset = ((prev + ((u32)data / sizeof(f32)))
        & ((32 -1) / sizeof(f32)));
 int seed = prev - offset;




 while (seed > 0) {
  ((seed <= rem) ? (void)0 : __assert("ecu_table.c", 32, "seed <= rem"));
  if (val < data[seed])
   seed -= 2 * 32 / sizeof(f32);
  else {
   data += seed;
   rem -= seed;
   goto search;
   break;
  }
 }

 if (__builtin_expect((!!(rem < 0 || data[0] >= data[1])),0)) {
  struct axis_current axis = { .index = 0, .percent = 0 };
  return axis;
 }

search:
 while (rem > 0 && data[1] < data[2]) {
  if (val < data[1])
   break;
  else {
   data++;
   rem--;
  }
 }

 struct axis_current axis;
 axis.percent = (val - data[0]) / (data[1] - data[0]);
 state->index = axis.index = cfg->num - (rem + 2);

 return axis;
}

static void find_index_f32_init(axis_f32_state *state,
    axis_f32_cfg *cfg, f32 val)
{
 ((cfg->num >= 2) ? (void)0 : __assert("ecu_table.c", 68, "cfg->num >= 2"));
 state->index = 0;
}

f32 interp_2d_f32(interp_2d_f32_state *state,
    interp_2d_f32_cfg *cfg, f32 x)
{
 struct axis_current axis = find_index_f32(&state->x, &cfg->x, x);
 const f32 *data = (f32 *)cfg->data + axis.index;
 return (data[1] - data[0]) * axis.percent + data[0];
}

void interp_2d_f32_init(interp_2d_f32_state *state,
     interp_2d_f32_cfg *cfg, f32 x)
{
 find_index_f32_init(&state->x, &cfg->x, x);
}

f32 interp_3d_f32(interp_3d_f32_state *state,
    interp_3d_f32_cfg *cfg, f32 x, f32 y)
{
 struct axis_current xaxis, yaxis;
 const f32 *data;
 f32 y0, y1;


 yaxis = find_index_f32(&state->y, &cfg->y, y);
 data = (f32 *)cfg->data + (yaxis.index * cfg->x.num);
 xaxis = find_index_f32(&state->x, &cfg->x, x);
 data += xaxis.index;
 y0 = (data[1] - data[0]) * xaxis.percent + data[0];
 data += cfg->x.num;
 y1 = (data[1] - data[0]) * xaxis.percent + data[0];
 return (y1 - y0) * yaxis.percent + y0;
}

void interp_3d_f32_init(interp_3d_f32_state *state,
   interp_3d_f32_cfg *cfg, f32 x, f32 y)
{
 find_index_f32_init(&state->x, &cfg->x, x);
 find_index_f32_init(&state->y, &cfg->y, y);
}

f32 interp_4d_f32(interp_4d_f32_state *state, interp_4d_f32_cfg *cfg,
    f32 x, f32 y, f32 z)
{
 struct axis_current xaxis, yaxis, zaxis;
 const f32 *data;
 f32 y0, y1, z0, z1;


 zaxis = find_index_f32(&state->z, &cfg->z, z);

 data = (f32 *)cfg->data + (zaxis.index * cfg->x.num * cfg->y.num);
 yaxis = find_index_f32(&state->y, &cfg->y, y);
 data += yaxis.index * cfg->x.num;
 xaxis = find_index_f32(&state->x, &cfg->x, x);
 data += xaxis.index;
 y0 = (data[1] - data[0]) * xaxis.percent + data[0];
 data += cfg->x.num;
 y1 = (data[1] - data[0]) * xaxis.percent + data[0];
 z0 = (y1 - y0) * yaxis.percent + y0;

 data += cfg->x.num * cfg->y.num;
 y1 = (data[1] - data[0]) * xaxis.percent + data[0];
 data -= cfg->x.num;
 y0 = (data[1] - data[0]) * xaxis.percent + data[0];
 z1 = (y1 - y0) * yaxis.percent + y0;
 return (z1 - z0) * zaxis.percent + z0;
}

void interp_4d_f32_init(interp_4d_f32_state *state, interp_4d_f32_cfg *cfg,
   f32 x, f32 y, f32 z)
{
 find_index_f32_init(&state->x, &cfg->x, x);
 find_index_f32_init(&state->y, &cfg->y, y);
 find_index_f32_init(&state->z, &cfg->z, z);
}
