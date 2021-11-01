main:
	ocamlbuild -use-ocamlfind mukanren.byte -tag thread
	./mukanren.byte

test:
	ocamlbuild -I src -use-ocamlfind mukanren.byte test.byte -tag thread
	./test.byte