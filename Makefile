OCAMLBUILD_CFLAGS = -cflags -g,-annot,"-warn-error +a"
OCAMLBUILD_MENHIRFLAGS = -use-menhir -menhir "menhir --explain"


default: smoketest


native:
	ocamlbuild -I src -lib unix $(OCAMLBUILD_MENHIRFLAGS) $(OCAMLBUILD_CFLAGS) tt.native

smoketest: native
	./tt.native examples/t.tt && \
	  ./tt.native examples/wild.tt && \
	  ./tt.native examples/brazil.tt && \
	  ./tt.native examples/brazilBool.tt && \
	  ./tt.native examples/evil.tt && \
	  ./tt.native examples/paths_to_id.tt
	@echo
	@echo "************************"
	@echo "* Smoke test succeeded *"
	@echo "************************"
	@echo


byte:
	ocamlbuild -I src -lib unix $(OCAMLBUILD_MENHIRFLAGS) $(OCAMLBUILD_CFLAGS) tt.byte

clean:
	ocamlbuild -clean

documentation:
	ocamlbuild -I src -use-menhir -docflag -keep-code -lib unix tt.docdir/index.html
