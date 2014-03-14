default: native

native:
	ocamlbuild -I src -lib unix -use-menhir -menhir "menhir --explain" -cflag -g -cflag -annot tt.native


byte:
	ocamlbuild -I src -lib unix -use-menhir tt.byte

clean:
	ocamlbuild -clean

documentation:
	ocamlbuild -I src -use-menhir -docflag -keep-code -lib unix tt.docdir/index.html
