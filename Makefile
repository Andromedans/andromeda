OCAMLBUILD_FLAGS = -cflags -g,-annot,"-warn-error +a"
OCAMLBUILD_MENHIRFLAGS = -use-menhir -menhir "menhir --explain"
#OCAMLBUILD_MENHIRFLAGS = -use-menhir -menhir "menhir --explain --trace"

all: andromeda.byte

default: andromeda.byte

andromeda.native:
	ocamlbuild -lib unix $(OCAMLBUILD_MENHIRFLAGS) $(OCAMLBUILD_FLAGS) andromeda.native

andromeda.byte: src/version.ml
	ocamlbuild -lib unix $(OCAMLBUILD_MENHIRFLAGS) $(OCAMLBUILD_FLAGS) andromeda.byte

# "make test" to see if anything broke
test: andromeda.byte
	cd tests && sh ./test.sh

# "make test-validate" to see if anything broke
# and ask for validation of possibly broken things.
test-validate: andromeda.byte
	cd tests && sh ./test.sh -v

src/version.ml:
	/bin/echo -n 'let version="' > src/version.ml
	git describe --always --long | tr -d '\n' >> src/version.ml
	/bin/echo '";;' >> src/version.ml

clean:
	ocamlbuild -clean

.PHONY: src/version.ml m31-smoketest clean andromeda.byte andromeda.native
