# Figure out which version of OCaml is being used
OCAML_VERSION=$(shell ocamlc --version)

# Figure out which version of sedlex is being used
SEDLEX_VERSION=$(shell opam info sedlex --version)

# Set up correct incantation for sedlex
SEDLEX=$(shell if [ "$(SEDLEX_VERSION)" \< "2.0" ] ; then echo "sedlex" ; else echo "sedlex.ppx"; fi)

#warnings disabled:
# 4: fragile pattern matching (we try to stick to it but don't always)
#27: innocuous unused variable
#29: non-escaped end-of-line in string constant
#50: unexpected documentation comment

# Use this to not die on all warnings
#OCAMLBUILD_FLAGS = -j 4 -lib unix -cflags -g,-annot,-w,+a-4-27-29-50 -use-ocamlfind -pkg menhirLib -pkg $(SEDLEX)

OCAMLBUILD_FLAGS = -j 4 -lib unix -cflags -g,-annot,-w,+a-4-27-29-50,"-warn-error +a" -use-ocamlfind -pkg menhirLib -pkg $(SEDLEX)

# The --strict flag prevents --explain, so we make a separate Makefile target to get
# menhir explanations
OCAMLBUILD_MENHIRFLAGS = -use-menhir -menhir "menhir --strict"
OCAMLBUILD_MENHIRFLAGS_EXPLAIN = -use-menhir -menhir "menhir --explain"

all: andromeda.native
opt: andromeda.native
default: andromeda.native
byte: andromeda.byte
debug: andromeda.d.byte
profile: andromeda.p.native

andromeda.byte andromeda.native andromeda.d.byte andromeda.p.native: src/build.ml
	ocamlbuild $(OCAMLBUILD_MENHIRFLAGS) $(OCAMLBUILD_FLAGS) $@

menhir-explain:
	ocamlbuild $(OCAMLBUILD_MENHIRFLAGS_EXPLAIN) $(OCAMLBUILD_FLAGS) src/parser/parser.ml

# "make test" to see if anything broke
test: default
	cd tests && sh ./test.sh

# "make test-validate" to see if anything broke
# and ask for validation of possibly broken things.
test-validate: default
	cd tests && sh ./test.sh -v

PREFIX ?= /usr
BIN_DIR ?= $(PREFIX)/bin
DOC_DIR ?= $(PREFIX)/doc
LIB_DIR ?= $(PREFIX)/lib
SHARE_DIR ?= $(PREFIX)/share
DOC_DIR := $(DOC_DIR)/andromeda-1
LIB_DIR := $(LIB_DIR)/andromeda-1
EXAMPLE_DIR := $(LIB_DIR)/examples

version:
	@git describe --always --long

src/build.ml:
	/bin/echo -n 'let version = "' > $@
	$(MAKE) -s version | egrep -v '^make' | tr -d '\n' >> $@
	/bin/echo '" ;;' >> $@
	echo "let lib_dir = \""$(LIB_DIR)"\" ;;" >> $@

emacs-autoloads:
	cd etc && emacs --batch --eval '(setq backup-inhibited t)' --eval '(update-file-autoloads "andromeda-1.el" t "'`pwd`'/andromeda-1-autoloads.el")'

andromeda.odocl:
	find src/ -name '*.mli' -exec basename {} '.mli' \; | perl -p -e 's/^(.)/\u\1/' > andromeda.odocl

doc: andromeda.odocl
	ocamlbuild $(OCAMLBUILD_FLAGS) andromeda.docdir/index.html

andromeda.docdir/andromeda.dot: andromeda.odocl
	ocamlbuild $(OCAMLBUILD_FLAGS) andromeda.docdir/andromeda.dot
	perl -i -p -e 's/digraph G/digraph Andromeda/; s/rotate=90;//' _build/andromeda.docdir/andromeda.dot

graph: andromeda.docdir/andromeda.dot
	dot -Tsvg < _build/andromeda.docdir/andromeda.dot > andromeda.svg


install: install-binary install-lib install-examples install-project-info install-emacs
uninstall: uninstall-binary uninstall-lib uninstall-examples uninstall-project-info uninstall-emacs

install-binary: opt
	install -d $(BIN_DIR)
	install _build/src/andromeda.native $(BIN_DIR)/andromeda-1
uninstall-binary:
	rm -f $(BIN_DIR)/andromeda-1

install-doc: doc
	install -d $(DOC_DIR)
	install -m 644 doc/theory.pdf $(DOC_DIR)/theory.pdf
uninstall-doc:
	rm -f $(DOC_DIR)/andromeda-theory.pdf
	rmdir $(DOC_DIR) || true

install-project-info:
	install -d $(DOC_DIR)
	install -m 644 README.markdown $(DOC_DIR)/README.markdown
uninstall-project-info:
	rm -f $(DOC_DIR)/README.markdown
	rmdir $(DOC_DIR) || true

install-emacs:
	install -d $(SHARE_DIR)/emacs/site-lisp
	install -m 644 etc/andromeda-1.el $(SHARE_DIR)/emacs/site-lisp
	install -m 644 etc/andromeda-1-autoloads.el $(SHARE_DIR)/emacs/site-lisp
	install -m 644 etc/andromeda-1-smie.el $(SHARE_DIR)/emacs/site-lisp
	install -m 644 etc/eri.el $(SHARE_DIR)/emacs/site-lisp
uninstall-emacs:
	rm -f $(SHARE_DIR)/emacs/site-lisp/andromeda-1.el $(SHARE_DIR)/emacs/site-lisp/andromeda-1-autoloads.el

install-lib:
	install -d $(LIB_DIR)/std
	install -m 644 prelude.m31 $(LIB_DIR)/prelude.m31
	cp -r std/* $(LIB_DIR)/std/
uninstall-lib:
	rm -rf $(LIB_DIR)/std/*
	rm -f $(LIB_DIR)/prelude.m31
	rmdir $(LIB_DIR) || true

install-examples:
	install -d $(EXAMPLE_DIR)
	cp -r examples/* $(EXAMPLE_DIR)
uninstall-examples:
	rm -rf $(EXAMPLE_DIR)/* || true
	rmdir $(EXAMPLE_DIR) || true

clean:
	ocamlbuild -clean

.PHONY: doc src/build.ml clean andromeda.byte andromeda.native version \
install install-binary install-doc install-examples install-lib uninstall \
andromeda.docdir/andromeda.dot andromeda.odocl
