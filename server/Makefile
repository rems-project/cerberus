HTTP_SERVER=simple_http_server.native

run: all
	./$(HTTP_SERVER) ../public 8000

all:
	ocamlbuild -use-ocamlfind -lib str $(HTTP_SERVER)