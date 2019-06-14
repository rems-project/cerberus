# We need CERB_PATH
ifndef CERB_PATH
$(error "Please set CERB_PATH.")
endif

include $(CERB_PATH)/Makefile.common

.PHONY: all clean

all:
	@make -C driver
	@make -C runtime

clean:
	@make -C driver clean
	@make -C runtime clean