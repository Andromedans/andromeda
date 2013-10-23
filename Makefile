default: native

native:
	ocamlbuild -lib unix -use-menhir -menhir "menhir --explain" tt.native

byte:
	ocamlbuild -lib unix -use-menhir tt.byte

clean:
	ocamlbuild -clean

doc:
	ocamlbuild -use-menhir -docflag -keep-code -lib unix tt.docdir/index.html
