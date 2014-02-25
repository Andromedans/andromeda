default: native

native:
	ocamlbuild -lib unix -use-menhir -menhir "menhir --explain" -cflag -g tt.native
	ocamlbuild -lib unix -use-menhir -menhir "menhir --explain" -cflag -g br.native


byte:
	ocamlbuild -lib unix -use-menhir tt.byte
	ocamlbuild -lib unix -use-menhir br.byte

clean:
	ocamlbuild -clean

doc:
	ocamlbuild -use-menhir -docflag -keep-code -lib unix tt.docdir/index.html
	ocamlbuild -use-menhir -docflag -keep-code -lib unix br.docdir/index.html
