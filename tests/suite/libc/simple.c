#include <assert.h>
#include <ctype.h>
#include <stdint.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <math.h>

void test_ctype()
{
  assert (isgraph('c') != 0);
  assert (isalpha('1') == 0);
  assert (isblank(' ') == 1);
  assert (iscntrl('c') == 0);
  assert (isdigit('1') == 1);
  assert (isgraph('1') == 1);
  assert (islower('c') == 1);
  assert (isprint('c') == 1);
  assert (ispunct('c') == 0);
  assert (isspace('c') == 0);
  assert (isupper('c') == 0);
  assert (isxdigit('c') == 1);
  assert (tolower('C') == 'c');
  assert (toupper('c') == 'C');
}

int cmpfunc(const void * a, const void * b) {
   return ( *(int*)a - *(int*)b );
}


void test_bsearch () {
  int values[] = { 5, 20, 29, 32, 63 };
  int *item;
  int key = 32;
  /* using bsearch() to find value 32 in the array */
  item = (int*) bsearch (&key, values, 5, sizeof (int), cmpfunc);
  if( item != NULL ) {
    printf("Found item = %d\n", *item);
  } else {
    printf("Item = %d could not be found\n", *item);
  }
  // Correct output: Found item = 32
}

void test_qsort () {
  int n;
  int values[] = { 88, 56, 100, 2, 25 };
  printf("Before sorting the list is: \n");
  for( n = 0 ; n < 5; n++ ) {
    printf("%d ", values[n]);
  }

  qsort(values, 5, sizeof(int), cmpfunc);

  printf("\nAfter sorting the list is: \n");
  for( n = 0 ; n < 5; n++ ) {   
    printf("%d ", values[n]);
  }
  // Correct output:
  // Before sorting the list is: 
  // 88 56 100 2 25 
  // After sorting the list is: 
  // 2 25 56 88 100
}

void test_stdlib()
{
  assert (atoi("42") == 42);
  assert (atol("42192830182301") == 42192830182301);
  assert (atoll("123123140523 rest  ... ") == 123123140523);
  //assert (atof("4.2") == 4.2);
  //assert (strtod ("4.2", NULL) == 4.2);
  //assert (strtof ("4.2", NULL) == 4.2);
  //assert (strtold ("4.2", NULL) == 4.2);
  assert (strtol("  0x1234 ", NULL, 16) == 0x1234);
  assert (strtoll("  0x1234  asdf ", NULL, 16) == 0x1234);
  assert (strtoul("  0xABC1234  asdf ", NULL, 16) == 0xABC1234);
  assert (strtoull("  0xABC1234  asdf ", NULL, 16) == 0xABC1234);
  assert (rand() >= 0);
  srand(42);
  int r = rand();
  srand(42);
  assert (r = rand());
  //assert (system ("SOMETHING") == 0); // no system processor
  test_bsearch();
  test_qsort();
  assert (abs (-42) == 42);
  assert (labs (-0xF) == 0xF);
  assert (llabs (0xA) == 0xA);
  // FIXME: div_t here has a different symbol than div_t in stdlib.h
  // TODO: link struct and union names somehow
  //div_t r = div (3, 2);
  //assert (r.quot = 1);
}

void test_stdio()
{
  FILE *f = fopen("test", "w+");
  char *text = "something to write!!";
  fwrite(text, 20, sizeof(char), f);
  fflush(f);
  putc('?', f);
  fclose(f);

  rename("test", "oldtest");

  f = fopen("oldtest", "r+");
  char buf[128];
  fread(buf, 20, sizeof(char), f);
  buf[20] ='\0';
  assert (strcmp(text, buf) == 0);
  fclose(f);

  remove("oldtest");

  f = tmpfile();
  char tiny_buf[1];
  setvbuf(f, tiny_buf, _IONBF, 1);
  fwrite(text, 20, sizeof(char), f);
  fprintf(f, "\nnumbers: %d, %x\n", 42, 0xAFu);

  fprintf(stderr, "error output!! %d\n", 0);

}

int main()
{
  test_ctype();
  test_stdlib();
  test_stdio();
}