// this test relates to issue #176 (https://github.com/rems-project/cerberus/issues/176)
union {
  short c1, c2;
} d;

short *glob_bug = &d.c2; // this global should not be lost in Core

short *glob_ok; 

int main(void) {
  return *glob_bug;
}