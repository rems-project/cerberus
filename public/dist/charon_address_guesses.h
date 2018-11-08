/*
ADDRESS_PFI_1I    pointer_from_integer_1i.c 
ADDRESS_PFI_1IG   pointer_from_integer_1ig.c                           
ADDRESS_PFI_1PG   pointer_from_integer_1pg.c                           
ADDRESS_PFI_2     pointer_from_integer_2.c                             
ADDRESS_PFI_2G    pointer_from_integer_2g.c                            
ADDR_PLE_1     provenance_lost_escape_1.c 
*/

/* older, not defined here:
  ADDR001    khmgzv-1.c
  ADDR002    khmgzv-2.c
  ADDR007    pointer_from_integer_static_1.c
  ADDR008    pointer_from_integer_2.c
  ADDR009    pointer_from_integer_2g.c
  ADDR010    pointer_from_integer_2_static.c
  ADDR011    pointer_from_integer_3.c
  ADDR012    pointer_from_integer_4.c
  ADDR013    pointer_from_integer_5.c
  ADDR014    pointer_from_integer_6.c
  ADDR015    pointer_from_integer_9.c
  ADDR016    pointer_from_integer_9b.c
  ADDR017    pointer_from_integer_10.c
  ADDR018    pointer_from_integer_11.c
  ADDR019    pointer_from_integer_11_nonstatic.c
  ADDR020    pointer_from_integer_13.c
  ADDR021    pointer_from_integer_13_static.c
  OFFS001    pointer_from_integer_7_victor.c
  ADDR001    pointer_from_integer_8.c
 */


#define MAYBE_PRINT // printf("&j=%p\n",(void*)&j);


#ifdef __cerb__
  #define ADDRESS_PFI_1I  0x20
  #define ADDRESS_PFI_1IG 0x28
  #define ADDRESS_PFI_1PG 0x30
  #define ADDRESS_PFI_1P  0x28
  #define ADDRESS_PFI_2   0x10
  #define ADDRESS_PFI_2G  0x14
  #define ADDR_PLE_1      0x3c

#elif defined __COMPCERT__
  #if !defined OPT
    #define ADDRESS_PFI_1PG 0x7fffffffe6d8 // km569 shell on limbus
    #define ADDRESS_PFI_1IG 0x7fffffffe6d8 // km569 shell on limbus
    #define ADDRESS_PFI_1P  42 // no-print (so not via charon)
    #define ADDRESS_PFI_1I  42 // no-print (so not via charon)
    #define ADDRESS_PFI_2   42 // no-print (so not via charon)
    #define ADDRESS_PFI_2G  0x7fffffffe6f8 // km569 shell on limbus
    #define ADDR_PLE_1      0x601040 // km569 shell on limbus
  #else
    #define ADDRESS_PFI_1IG 0x7fffffffe6d8 // km569 shell on limbus
    #define ADDRESS_PFI_1PG 0x7fffffffe6d8 // km569 shell on limbus
    #define ADDRESS_PFI_1P  42 // no-print (so not via charon)
    #define ADDRESS_PFI_1I  42 // no-print (so not via charon)
    #define ADDRESS_PFI_2   42 // no-print (so not via charon)
    #define ADDRESS_PFI_2G  0x7fffffffe6e8 // km569 shell on limbus
    #define ADDR_PLE_1      0x601040 // km569 shell on limbus
  #endif

#elif defined GCC81
  #if OPT == 0 && GCC_ALLOC_VERSION == 0
    #define ADDRESS_PFI_1PG 0x7fffffffdc0c
    #define ADDRESS_PFI_1IG 0x7fffffffdc04
    #define ADDRESS_PFI_1P  42 // no-print (so not via charon)
    #define ADDRESS_PFI_1I  42 // no-print (so not via charon)
    #define ADDRESS_PFI_2   42 // no-print (so not via charon)
    #define ADDRESS_PFI_2G  0x7fffffffdc2c
    #define ADDR_PLE_1   0x600a50
  #elif (OPT == 2 || OPT == 3) && GCC_ALLOC_VERSION == 0
    #if !defined NO_STRICT_ALIASING
      #define ADDRESS_PFI_1PG 0x7fffffffdc2c
      #define ADDRESS_PFI_1IG 0x7fffffffdc2c
      #define ADDRESS_PFI_1P  42 // dummy address (lost by opt)
      #define ADDRESS_PFI_1I  0x7fffffffe6bc // dummy address (lost by opt)
      #define ADDRESS_PFI_2   42 // dummy address (lost by opt)
      #define ADDRESS_PFI_2G  0x7fffffffdc2c
      #define ADDR_PLE_1   0x6009a8
    #else
      #define ADDRESS_PFI_1PG 0x7fffffffdc0c
      #define ADDRESS_PFI_1IG 0x7fffffffdc0c
      #define ADDRESS_PFI_1P  42 // dummy address (lost by opt)
      #define ADDRESS_PFI_1I  0x7fffffffe6bc // dummy address (lost by opt)
      #define ADDRESS_PFI_2   42 // dummy address (lost by opt)
      #define ADDRESS_PFI_2G  0x7fffffffdc0c
      #define ADDR_PLE_1   0x6009a8
    #endif
  #endif
  
#elif defined CLANG60
  #if CLANG_ALLOC_VERSION == 0
    #define ADDRESS_PFI_1PG 0x7fffffffdbc4
    #define ADDRESS_PFI_1IG 0x7fffffffdbc4
    #define ADDRESS_PFI_1P  42 // no-print (so not via charon)
    #define ADDRESS_PFI_1I  0x7fffffffe6b4 // no-print (so not via charon)
    #define ADDRESS_PFI_2   42 // no-print (so not via charon)
    #define ADDRESS_PFI_2G  0x7fffffffdbe8
    #define ADDR_PLE_1   0x601038
  #elif (OPT == 2 || OPT == 3) && !defined UBSAN && !defined ASAN && !defined MSAN && CLANG_ALLOC_VERSION == 0
    #if !defined    NO_STRICT_ALIASING
      #define ADDRESS_PFI_1PG 0x7fffffffdbf4
      #define ADDRESS_PFI_1IG 0x7fffffffdbf4
      #define ADDRESS_PFI_1P  42 // dummy address (lost by opt)
      #define ADDRESS_PFI_1I  0x7fffffffe6b4 // dummy address (lost by opt)
      #define ADDRESS_PFI_2   42 // dummy address (lost by opt)
      #define ADDRESS_PFI_2G  0x7fffffffdbf4
      #define ADDR_PLE_1   0x601038
    #else
      #define ADDRESS_PFI_1PG 0x7fffffffdbd4
      #define ADDRESS_PFI_1IG 0x7fffffffe674 
      #define ADDRESS_PFI_1P  42 // dummy address (lost by opt)
      #define ADDRESS_PFI_1I  0x7fffffffe6b4 // dummy address (lost by opt)
      #define ADDRESS_PFI_2   42 // dummy address (lost by opt)
      #define ADDRESS_PFI_2G  0x7fffffffdbd4
      #define ADDR_PLE_1   0x601038
    #endif
  #elif defined UBSAN && OPT == 2 && CLANG_ALLOC_VERSION == 0
    #define ADDRESS_PFI_1PG 0x7fffffffdbf4
    #define ADDRESS_PFI_1IG 0x7fffffffdbf4
    #define ADDRESS_PFI_1P  42 // no-print (so not via charon)
    #define ADDRESS_PFI_1I  0x7fffffffe6b4 // no-print (so not via charon)
    #define ADDRESS_PFI_2   42 // no-print (so not via charon)
    #define ADDRESS_PFI_2G  0x7fffffffdbf4
    #define ADDR_PLE_1   0x631b50
  #elif defined ASAN && OPT == 2 && CLANG_ALLOC_VERSION == 0
    #define ADDRESS_PFI_1PG 0x7fffffffdb60
    #define ADDRESS_PFI_1IG 0x7fffffffdb60
    #define ADDRESS_PFI_1P  42 // no-print (so not via charon)
    #define ADDRESS_PFI_1I  0x7fffffffe6b4 // no-print (so not via charon)
    #define ADDRESS_PFI_2   42 // no-print (so not via charon)
    #define ADDRESS_PFI_2G  0x7fffffffdb60
    #define ADDR_PLE_1   0x716b60
  #elif defined UBSAN && OPT == 2 && CLANG_ALLOC_VERSION == 0
    #define ADDRESS_PFI_1PG 0x7fffffffdbec
    #define ADDRESS_PFI_1IG 0x7fffffffdbec
    #define ADDRESS_PFI_1P  42 // no-print (so not via charon)
    #define ADDRESS_PFI_1I  0x7fffffffe6b4 // no-print (so not via charon)
    #define ADDRESS_PFI_2   42 // no-print (so not via charon)
    #define ADDRESS_PFI_2G  0x7fffffffdbec
    #define ADDR_PLE_1   0x6b7af0
#endif

#elif defined ICC19
  #if OPT == 0 && ICC_ALLOC_VERSION == 0
    #define ADDRESS_PFI_1PG 0x7fffffffdc00
    #define ADDRESS_PFI_1IG 0x7fffffffdbf0
    #define ADDRESS_PFI_1P  42 // no-print (so not via charon)
    #define ADDRESS_PFI_1I  0x7fffffffe6a0 // no-print (so not via charon)
    #define ADDRESS_PFI_2   42 // no-print (so not via charon)
    #define ADDRESS_PFI_2G  0x7fffffffdc20
    #define ADDR_PLE_1   0x600b70
  #elif (OPT == 2 || OPT == 3) && ICC_ALLOC_VERSION == 0
    #if !defined    NO_STRICT_ALIASING
      #define ADDRESS_PFI_1PG 0x7fffffffdb84
      #define ADDRESS_PFI_1IG 0x7fffffffdb84
      #define ADDRESS_PFI_1P  42 // dummy address (lost by opt)
      #define ADDRESS_PFI_1I  0x7fffffffe6a0 // dummy address (lost by opt)
      #define ADDRESS_PFI_2   42 // dummy address (lost by opt)
      #define ADDRESS_PFI_2G  0x6046c0
      #define ADDR_PLE_1   0x6046c0
    #else
      #define ADDRESS_PFI_1PG 0x7fffffffdb84
      #define ADDRESS_PFI_1IG 0x7fffffffdb84
      #define ADDRESS_PFI_1P  42 // dummy address (lost by opt)
      #define ADDRESS_PFI_1I  0x7fffffffe6a0 // dummy address (lost by opt)
      #define ADDRESS_PFI_2   42 // dummy address (lost by opt)
      #define ADDRESS_PFI_2G  0x6046c0
      #define ADDR_PLE_1   0x6046c0
    #endif
  #endif
  
#else
#error this compiler is not supported by charon_address_guesses.h
#endif
