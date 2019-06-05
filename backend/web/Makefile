# We need CERB_PATH
ifndef CERB_PATH
$(error "Please set CERB_PATH.")
endif

include $(CERB_PATH)/Makefile.common

.PHONY: all clean

all:
	@echo $(BOLD)BUILDING Web Concrete Instance$(RESET)
	@make -C concrete
	@echo $(BOLD)BUILDING Web Symbolic Instance$(RESET)
	@make -C symbolic
	@echo $(BOLD)BUILDING Web Server$(RESET)
	@make -C server

clean:
	@make -C concrete clean
	@make -C symbolic clean
	@make -C server clean
