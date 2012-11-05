all:
	ocamlbuild -lib unix -use-menhir tt.native

clean:
	ocamlbuild -clean
