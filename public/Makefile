# We need npm
ifeq (, $(shell which npm))
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

