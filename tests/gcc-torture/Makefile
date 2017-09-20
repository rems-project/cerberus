transform.native:
	ocamlbuild -pkg cil transform.native

.PHONY: sorted
sorted: transform.native cerberus.h
	rm -rf sorted
	./run.sh