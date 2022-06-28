#ifndef __CHERIINTRIN_H
#define __CHERIINTRIN_H

#ifndef __CHERI__
#error "<cheriintrin.h> should only be included when using the CHERI memory model"
#endif

#define cheri_perms_and  __cerbvar_cheri_perms_and
#define cheri_address_get __cerbvar_cheri_address_get
#define cheri_offset_get __cerbvar_cheri_offset_get
#define cheri_base_get __cerbvar_cheri_base_get
#define cheri_length_get __cerbvar_cheri_length_get
#define cheri_tag_get __cerbvar_cheri_tag_get
#define cheri_tag_clear __cerbvar_cheri_tag_clear
#define cheri_is_equal_exact __cerbvar_cheri_is_equal_exact
#define cheri_representable_length __cerbvar_cheri_representable_length
#define cheri_representable_alignment_mask __cerbvar_cheri_representable_alignment_mask

#endif
