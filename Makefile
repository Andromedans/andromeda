OCAMLBUILD_FLAGS = -cflags -g,-annot,"-warn-error +a" -use-ocamlfind -pkgs delimcc
OCAMLBUILD_MENHIRFLAGS = -use-menhir -menhir "menhir --explain"
#OCAMLBUILD_MENHIRFLAGS = -use-menhir -menhir "menhir --explain --trace"



all: brazil.byte tt.byte tt-smoketest

default: tt.byte

brazil.native:
	ocamlbuild -lib unix $(OCAMLBUILD_MENHIRFLAGS) $(OCAMLBUILD_FLAGS) brazil.native

brazil.byte:
	ocamlbuild -lib unix $(OCAMLBUILD_MENHIRFLAGS) $(OCAMLBUILD_FLAGS) brazil.byte

tt.native:
	ocamlbuild -lib unix $(OCAMLBUILD_MENHIRFLAGS) $(OCAMLBUILD_FLAGS) tt.native

tt.byte:
	ocamlbuild -lib unix $(OCAMLBUILD_MENHIRFLAGS) $(OCAMLBUILD_FLAGS) tt.byte

tt-smoketest: tt.byte
	./tt.byte examples/eff.tt 
	./tt.byte examples/literals.tt 
	./tt.byte examples/nat.tt 
	./tt.byte examples/equality.tt
	@echo
	@echo "***************************"
	@echo "* TT Smoke test succeeded *"
	@echo "***************************"
	@echo


clean:
	ocamlbuild -clean

.PHONY: tt-smoketest clean brazil.byte brazil.native tt.byte tt.native
