OCAMLBUILD_FLAGS = -cflags -g,-annot,"-warn-error +a"
OCAMLBUILD_MENHIRFLAGS = -use-menhir -menhir "menhir --explain"
#OCAMLBUILD_MENHIRFLAGS = -use-menhir -menhir "menhir --explain --trace"



all: br-smoketest #tt-smoketest

default: tt.byte

brazil.native:
	ocamlbuild -lib unix $(OCAMLBUILD_MENHIRFLAGS) $(OCAMLBUILD_FLAGS) brazil.native

brazil.byte:
	ocamlbuild -lib unix $(OCAMLBUILD_MENHIRFLAGS) $(OCAMLBUILD_FLAGS) brazil.byte

br-smoketest: brazil.byte
	./brazil.byte examples/bool.br
	./brazil.byte examples/nat.br
	./brazil.byte examples/sigma.br
	@echo
	@echo "*******************************"
	@echo "* Brazil Smoke Test succeeded *"
	@echo "*******************************"
	@echo

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
	@echo "* TT Smoke Test succeeded *"
	@echo "***************************"
	@echo


clean:
	ocamlbuild -clean

.PHONY: tt-smoketest br-smoketest clean brazil.byte brazil.native tt.byte tt.native
