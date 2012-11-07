all:
	ocamlbuild -lib unix -use-menhir tt.native

clean:
	ocamlbuild -clean

doc:
	ocamlbuild -use-menhir -docflag -keep-code -lib unix tt.docdir/index.html
