# BMC Toyota Tests

`defects.txt` and `wo_defects.txt` contains a (very) initial run of the BMC on Toyota
tests, reporting SAT, UNSAT, or ERROR (a BMC assertion failure/timeout).

There are many sources of possible errors, some of which are:
- use of `rand()`: we have not provided a definition for this yet
- use of doubles/floats
- currently unsupported operations: bitwise operations, modulus, exponentiation
- use of structs as values 
- pointer type-casting
- use of printf
- loop bounds exceeding BMC's max loop limit
- not having added the appropriate #include (oops)

# TODO
- Go through tests to make sure they were generated correctly
- Rewrite any necessary parts (e.g. rand or printf)
- Identity sources of errors
- Fix the trivial sources of error
- ... fix the less trivial sources of error 

# Files ignored

For now, we ignore anything with
- pthreads

Files ignored:

| File | Reason |
| ---- | -------|
| dead_lock | pthreads |
| double_lock | pthreads |
| double_release | pthreads |
| livelock | pthreads |
| lock_never_unlock | pthreads |
| race_condition | pthreads |
| sleep_lock | pthreads |
| st_cross_thread_access | pthreads | 
| unlock_without_lock | pthreads |


