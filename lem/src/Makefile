PATH := $(CURDIR)/../findlib-1.2.7/bin:$(PATH)

all:
	ocamlbuild -use-ocamlfind main.native

debug: 
	ocamlbuild -use-ocamlfind main.d.byte

clean:
	-ocamlbuild -clean
	-rm -rf _build
