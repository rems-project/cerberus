default: patch_lem

patch_lem:
	patch -t -d ../../lem -p0 -i ../csem/patches/lem_compare_hack.patch
	make -C ../../lem

unpatch_lem:
	patch -R -t -d ../../lem -p0 -i ../csem/patches/lem_compare_hack.patch
	make -C ../../lem