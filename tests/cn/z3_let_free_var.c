// This is a test which happens to trigger Z3 (4.13.0) produce a particular
// kind of let-binding in a response, thus exposing a bug in the free variable calculation
// This bug was fixed in the below commit, but without a repro/test
// (the bug was discovered on an incomplete feature branch)
// https://github.com/rems-project/cerberus/commit/4e7fcb9f29eb9f7bbc49c092c2850f7da9e8dd66

struct state {
    // they also need to be these types for some reason
    int need[3];
    int all[3];
    int of[3];
    char these[3];
};
void foo(struct state *state);
/*@ spec foo(pointer state);
  requires
  take statein = Owned(state);
  each(u64 j; j < (u64)3u8) {statein.these[j] < 3u8};
  ensures
  take stateout = Owned(state);
  @*/

static int bar(struct state *state);
/*@ spec bar(pointer state);
  requires
  true;
  take si = Owned(state);
  each(u64 j;0u64 <= j && j < (u64)3u8) { si.these[j] < 3u8};
  ensures
  true;
  take so = Owned(state);
  each(u64 j;0u64 <= j && j < (u64)3u8) { so.these[j] < 3u8};
  @*/
static int baz(struct state *state);
/*@ spec baz(pointer state);
  requires
  true;
  ensures
  take s_out = Owned(state);
  each(u64 i; 0u64 <= i && i < (u64)3u8) { s_out.these[i] < 3u8};
  @*/
static int qux(struct state *state) ;
/*@ spec qux(pointer state);
  requires
  true;
  ensures
  return <= 0i32;
  take so = Owned(state);
  @*/
void foo(struct state *state)
{
    bar(state);
    baz(state);
    qux(state);
}
