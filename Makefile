OCAMLBUILD_FLAGS = -cflags -g,-annot,"-warn-error +a" -use-ocamlfind -pkg menhirLib -pkg sedlex
OCAMLBUILD_MENHIRFLAGS = -use-menhir -menhir "menhir --explain"
#OCAMLBUILD_MENHIRFLAGS = -use-menhir -menhir "menhir --explain --trace"

all: andromeda.byte
opt: andromeda.native
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

PREFIX ?= /usr
BIN_DIR ?= $(PREFIX)/bin
DOC_DIR ?= $(PREFIX)/doc
DOC_DIR := $(DOC_DIR)/andromeda
LIB_DIR ?= $(PREFIX)/lib
LIB_DIR := $(LIB_DIR)/andromeda

install: install-binary install-lib install-examples

install-binary: opt
	install -D _build/src/andromeda.native $(BIN_DIR)/andromeda

install-examples:
	install -d $(DOC_DIR)/examples
	install -m644 examples/* $(DOC_DIR)/examples/

install-doc: doc
	install -d $(DOC_DIR)
	install -m a-x doc/theory.pdf $(DOC_DIR)/theory.pdf

install-lib:
	install -d $(LIB_DIR)
	install -m 644 prelude.m31 $(LIB_DIR)/prelude.m31

uninstall:
	rm -f $(BIN_DIR)/andromeda $(DOC_DIR)/andromeda-theory.pdf $(LIB_DIR)/prelude.m31
	rm -r $(DOC_DIR)/examples || true
	rmdir $(DOC_DIR) || true
	rmdir $(LIB_DIR) || true

src/version.ml:
	/bin/echo -n 'let version="' > src/version.ml
	git describe --always --long | tr -d '\n' >> src/version.ml
	/bin/echo '";;' >> src/version.ml

doc: default
	cd doc && latex -output-format pdf theory.tex
	/bin/mkdir -p ./doc/html
	ocamlbuild -docflag "-d" -docflag "doc/html" doc/andromeda.docdir/index.html

clean:
	ocamlbuild -clean

.PHONY: doc src/version.ml clean andromeda.byte andromeda.native
