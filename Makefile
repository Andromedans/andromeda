OCAMLBUILD_CFLAGS = -cflags -g,-annot,"-warn-error +a"
OCAMLBUILD_MENHIRFLAGS = -use-menhir -menhir "menhir --explain"


default: brazil.byte

all: brazil.byte tt.byte

brazil.native:
	ocamlbuild -cflag -absname -I brazil -lib unix $(OCAMLBUILD_MENHIRFLAGS) $(OCAMLBUILD_CFLAGS) brazil.native

brazil.byte:
	ocamlbuild -cflag -absname -I brazil -lib unix $(OCAMLBUILD_MENHIRFLAGS) $(OCAMLBUILD_CFLAGS) brazil.byte

tt.native:
	ocamlbuild -I src -lib unix $(OCAMLBUILD_MENHIRFLAGS) $(OCAMLBUILD_CFLAGS) tt.native

tt.byte:
	ocamlbuild -I src -lib unix $(OCAMLBUILD_MENHIRFLAGS) $(OCAMLBUILD_CFLAGS) tt.byte

smoketest: tt.byte
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


clean:
	ocamlbuild -clean

.PHONY: smoketest clean brazil.byte brazil.native tt.byte tt.native
