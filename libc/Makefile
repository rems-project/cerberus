SRC=src/ctype.c \
		src/stdio.c \
		src/stdlib.c \
		src/string.c \
		src/time.c

libc.co: $(SRC)
	cerberus --nostdlibinc -I include -I include/posix --rewrite -c $^ -o $@

clean:
	rm -rf libc.co