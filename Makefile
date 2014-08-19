OCAMLBUILD_FLAGS = -cflags -g,-annot,"-warn-error +a"
OCAMLBUILD_MENHIRFLAGS = -use-menhir -menhir "menhir --explain"
#OCAMLBUILD_MENHIRFLAGS = -use-menhir -menhir "menhir --explain --trace"

all: m31-smoketest #tt-smoketest

default: tt.byte

andromeda.native:
	ocamlbuild -lib unix $(OCAMLBUILD_MENHIRFLAGS) $(OCAMLBUILD_FLAGS) andromeda.native

andromeda.byte:
	ocamlbuild -lib unix $(OCAMLBUILD_MENHIRFLAGS) $(OCAMLBUILD_FLAGS) andromeda.byte

m31-smoketest: andromeda.byte
	./andromeda.byte examples/bool.m31
	./andromeda.byte examples/nat.m31
	./andromeda.byte examples/records.m31
# ./andromeda.byte examples/sigma.m31
	@echo
	@echo "**********************************"
	@echo "* Andromeda Smoke Test succeeded *"
	@echo "**********************************"
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

.PHONY: tt-smoketest m31-smoketest clean andromeda.byte andromeda.native tt.byte tt.native
