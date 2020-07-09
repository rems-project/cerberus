#include <stdint.h>
int glob;

int *p;

/*
void f(int param)
{
  int x;
  p = &param;
  p = &x;
}
*/

int cond;

int *p;

int *global_ptr;

void *fptr;

void f(int param)
{
  int *local_ptr;
  int **local_ptr_ptr = &global_ptr;
  local_ptr = &param; // SAFE
  *local_ptr_ptr = &param; // maybe UNSAFE
  
//  fptr = (void*)&f; // TODO: the classify function need to properly report &f as pointing to a function
}

void g(int param)
{
//  int **q;
//  *q = cond ? p : p;
  int x;
  *p = (intptr_t)&x; // UNSAFE
}


void h(int *param_ptr, int **param_ptr_ptr, int param)
{
  param_ptr = &param; // SAFE
  *param_ptr_ptr = &param; // UNSAFE
}


int **global_ptr_ptr;

void i(void)
{
  int local;
  int *local_ptr;
  {
    int current;
    int *current_ptr;

    current_ptr = &glob; // SAFE
    local_ptr = &glob;   // SAFE
    global_ptr = &glob;  // SAFE
    
    current_ptr = &local; // SAFE
    local_ptr = &local;   // SAFE
    global_ptr = &local;  // UNSAFE
    
    current_ptr = &current; // SAFE
    local_ptr = &current;   // UNSAFE
    global_ptr = &current;  // UNSAFE
    
//    &(1? (glob : current);
    current_ptr = (int*) (1 ? (intptr_t)&glob : (intptr_t)&current); // SAFE
    local_ptr = (int*) (1 ? (intptr_t)&glob : (intptr_t)&current); // UNSAFE
    global_ptr = (int*) (1 ? (intptr_t)&glob : (intptr_t)&current); // UNSAFE
    
    local_ptr = (int*) (1 ? (intptr_t)&glob : (intptr_t)&local); // SAFE
    global_ptr = (int*) (1 ? (intptr_t)&glob : (intptr_t)&current); // UNSAFE
    
    
    int **current_ptr_ptr;
    *current_ptr_ptr = &local; // UNSAFE
  }
}


int* global_arr[2];

void j(void)
{
  {
    int *current_ptr1, *current_ptr2;
    int current;
//    global_arr[0] = &current;
    global_ptr = &current + 1; // UNSAFE
    global_ptr = (current_ptr1 = &current); // UNSAFE
    current_ptr2 = (current_ptr1 = &current); // SAFE
  }
}


void k(void)
{
    int *p;
  {
    int x, y, *ptr;
    ptr = &x;
    
    global_ptr = ptr; // UNSAFE (ptr contains the address of x)

  }
  
  *global_ptr; // this is ub
}


int glob2 = 1;
uintptr_t glob3 = 12;
uintptr_t *glob_ptr2 = &glob3;


int l(void) {
  int *p;
  {
    uintptr_t x = 42;
    *(glob2 ? glob_ptr2 : &x) = (uintptr_t)&x; // UNSAFE
  }
  *(int*)*glob_ptr2; // THIS IS UB
}


int m(void) {
  int *p;
  {
    int x, y, *ptr;
    p = &(*&x);              // UNSAFE
    p = &(*(glob? &x : &y)); // UNSAFE
    p = &x;                  // UNSAFE
    
    *(&x) = (int)&x; // SAFE
    *global_ptr = (int)&x; // UNSAFE
    *(glob? global_ptr : &x) = (int)&x; // UNSAFE
  }
  
  *global_ptr; // THIS IS UB
}


int *glob4;
int **glob5;

int n(void)
{
  {
    int x;
    int *p;
    int **q;
    p = &x;
    q = &p;
    glob5 = &*q; // UNSAFE
  }
  **glob5;
}


int o(void)
{
  {
    int x;
    int *p = &x;
    int **q  = &p;
    glob5 = &*q; // UNSAFE
  }
  **glob5;
}
