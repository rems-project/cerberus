#include <stdio.h>

// global arrays with unknown size on the left side
int glob_b2[] = {1};
int glob_b3[] = {1,2};
int glob_b4[] = {1,[2]=3};


int main(void)
{
  printf("glob_b2[%lu]= {%d}\n",
    sizeof(glob_b2)/sizeof(int), glob_b2[0]);
  printf("glob_b3[%lu]= {%d, %d}\n",
    sizeof(glob_b3)/sizeof(int), glob_b3[0], glob_b3[1]);
  printf("glob_b4[%lu]= {%d, %d, %d}\n",
    sizeof(glob_b4)/sizeof(int), glob_b4[0], glob_b4[1], glob_b4[2]);
}
