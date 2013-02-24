all:
	ocamlbuild main.native

debug: 
	ocamlbuild -package str main.d.byte

clean:
	-ocamlbuild -clean
	-rm -rf _build
