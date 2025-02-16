SRC_DIR := ./src

SRCS := $(shell find $(SRC_DIR) -name '*.c')
TESTS := $(SRCS:%=testing-%)

test: $(TESTS)

$(TESTS): testing-%: %
	./run-single-test.sh $<
