# PNVI-ae-udi/VIP testsuite adapted for CN
---
* VIP does not have non-det. pointer equality but CN does
* The addition of ghost parameters to CN may increase the expressiveness of the memory model

## To do
* Add support round trip casts
* Add support preserving pointer provenance via bytes
* Add support memcpy_proxy
* Add support unions
* Fix peformance bug for pointer\_copy\_user\_ctrflow\_bytewise.c
* `tests/cn_vip_testsuite/provenance_tag_bits_via_repr_byte_1.pass.c:1:// NOTE: terminates with cvc5 but not Z3`
* `tests/cn_vip_testsuite/provenance_tag_bits_via_uintptr_t_1.annot.c:1:// NOTE: terminates with cvc5 but not Z3`
