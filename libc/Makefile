Z3_PATH   := $(shell ocamlfind query z3)
CERB_PATH ?= ..
DYLD_LIBRARY_PATH = ${Z3_PATH}
LD_LIBRARY_PATH   = /usr/local/lib:${Z3_PATH}

SRC_C=src/ctype.c \
		src/stdio.c \
		src/stdlib.c \
		src/string.c \
		src/time.c \
		src/utime.c \
		src/unistd.c \
		src/stat.c \
		src/uio.c \
		src/internal.c \
		src/vfscanf.c \
		src/signal.c

SRC_M=src/math.c

all: libc.co libm.co

libc.co: $(SRC_C)
	OCAMLRUNPARAM=b CERB_PATH=$(CERB_PATH) LD_LIBRARY_PATH=$(LD_LIBRARY_PATH) DYLD_LIBRARY_PATH=$(DYLD_LIBRARY_PATH) ../cerberus --nolibc -I include -I include/posix --rewrite $^ -o $@

libm.co: $(SRC_M)
	OCAMLRUNPARAM=b CERB_PATH=$(CERB_PATH) LD_LIBRARY_PATH=$(LD_LIBRARY_PATH) DYLD_LIBRARY_PATH=$(DYLD_LIBRARY_PATH) ../cerberus --nolibc -I include -I include/posix --rewrite $^ -o $@

clean:
	rm -rf libc.co libm.co
