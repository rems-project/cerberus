#ifndef __CHERIINTRIN_H
#define __CHERIINTRIN_H

#ifndef __CHERI__
#error "<cheriintrin.h> should only be included when using the CHERI memory model"
#endif

#define cheri_perms_and  __cerbvar_cheri_perms_and

#endif