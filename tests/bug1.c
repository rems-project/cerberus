// #include "random_runtime.h"
#include <stdio.h>
#include <stdint.h>
#include <limits.h>


/* #define safe_lshift_func_int8_t_s_u(left,_left,right,_right) \ */
/*   ((int8_t)( left = (_left), right = (_right) , \ */
/*    ( \ */
/*    (((unsigned int)(right)) >= sizeof(int8_t)*CHAR_BIT) \ */
/*    ) \ */
/*   ? ((int8_t)(left)) \ */
/*   : (((int8_t)(left)) << ((unsigned int)(right))))) */


static int8_t
(safe_lshift_func_int8_t_s_u)(int8_t left, unsigned int right)
{
  return

    ((left < 0) || (((unsigned int)right) >= 32) || (left > (INT8_MAX >> ((unsigned int)right)))) ?
    ((left)) :

    (left << ((unsigned int)right));
}


int32_t g_6 = 0x10B999FBL;
int32_t * volatile g_5 = &g_6;

uint16_t  func_1(void);

uint16_t  func_1(void)
{
    int32_t l_4 = 7L;
    int32_t *l_8 = &g_6;
    int32_t **l_7 = &l_8;
    (*g_5) = (safe_lshift_func_int8_t_s_u(l_4, 0x2CFB6318L));
    (*l_7) = 0;
    return l_4;
}

void g(void)
{
    int32_t l_4 = 7L;
    (*g_5) = (safe_lshift_func_int8_t_s_u(l_4, 0x2CFB6318L));

}


int main (int argc, char* argv[])
{
//    func_1();
  g();
  printf("checksum g_6 = %d\n", g_6);
}
