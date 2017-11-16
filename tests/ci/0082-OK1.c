#include <stdio.h>

// global array with fixed size
int glob_a2[2] = {1};
int glob_a3[2] = {1,2};
int glob_a4[3] = {1,[2]=3};


int main(void)
{
  printf("glob_a2[%lu]= {%d, %d}\n",
    sizeof(glob_a2)/sizeof(int), glob_a2[0], glob_a2[1]);
  printf("glob_a3[%lu]= {%d, %d}\n",
    sizeof(glob_a3)/sizeof(int), glob_a3[0], glob_a3[1]);
  printf("glob_a4[%lu]= {%d, %d, %d}\n",
    sizeof(glob_a4)/sizeof(int), glob_a4[0], glob_a4[1], glob_a4[2]);
}
