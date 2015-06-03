OCAMLBUILD_FLAGS = -cflags -g,-annot,"-warn-error +a"
OCAMLBUILD_MENHIRFLAGS = -use-menhir -menhir "menhir --explain"
#OCAMLBUILD_MENHIRFLAGS = -use-menhir -menhir "menhir --explain --trace"

all: andromeda.byte
default: andromeda.byte
debug: andromeda.d.byte
profile: andromeda.p.native

andromeda.byte andromeda.native andromeda.d.byte andromeda.p.native: src/version.ml
	ocamlbuild -lib unix $(OCAMLBUILD_MENHIRFLAGS) $(OCAMLBUILD_FLAGS) $@

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

doc: default
	/bin/mkdir -p ./doc/html
	ocamlbuild -docflag "-d" -docflag "doc/html" doc/andromeda.docdir/index.html

clean:
	ocamlbuild -clean

.PHONY: doc src/version.ml clean andromeda.byte andromeda.native
