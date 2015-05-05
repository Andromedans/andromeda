OCAMLBUILD_FLAGS = -cflags -g,-annot,"-warn-error +a"
OCAMLBUILD_MENHIRFLAGS = -use-menhir -menhir "menhir --explain"
#OCAMLBUILD_MENHIRFLAGS = -use-menhir -menhir "menhir --explain --trace"

all: m31-smoketest #tt-smoketest

default: andromeda.byte

andromeda.native:
	ocamlbuild -lib unix $(OCAMLBUILD_MENHIRFLAGS) $(OCAMLBUILD_FLAGS) andromeda.native

andromeda.byte: src/version.ml
	ocamlbuild -lib unix $(OCAMLBUILD_MENHIRFLAGS) $(OCAMLBUILD_FLAGS) andromeda.byte

m31-smoketest: andromeda.byte
	./andromeda.byte examples/bool.m31
	./andromeda.byte examples/nat.m31
	./andromeda.byte examples/records.m31
	./andromeda.byte examples/list.m31
# ./andromeda.byte examples/sigma.m31
	@echo
	@echo "**********************************"
	@echo "* Andromeda Smoke Test succeeded *"
	@echo "**********************************"
	@echo

src/version.ml:
	/bin/echo -n 'let version="' > src/version.ml
	git describe --always --long | tr -d '\n' >> src/version.ml
	/bin/echo '";;' >> src/version.ml

clean:
	ocamlbuild -clean

.PHONY: src/version.ml m31-smoketest clean andromeda.byte andromeda.native
