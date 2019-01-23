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
	cerberus --nolibc -I include -I include/posix --rewrite $^ -o $@

libm.co: $(SRC_M)
	cerberus --nolibc -I include -I include/posix --rewrite $^ -o $@

clean:
	rm -rf libc.co libm.co