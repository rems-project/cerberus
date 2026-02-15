# We need npm
ifeq (,$(shell command -v npm 2> /dev/null))
$(error "npm is required to build the UI part of Cerberus")
endif

.PHONY: start build deploy

all: build

start: node_modules
	npm run start

build: node_modules
	npm run build

deploy: node_modules
	npm run deploy

node_modules:
	npm install

