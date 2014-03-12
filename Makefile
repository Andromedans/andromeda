default: native

native:
	ocamlbuild -I src -lib unix -use-menhir -menhir "menhir --explain" -cflag -g tt.native


byte:
	ocamlbuild -I src -lib unix -use-menhir tt.byte

clean:
	ocamlbuild -clean

#doc:
#	ocamlbuild -I src -use-menhir -docflag -keep-code -lib unix tt.docdir/index.html
