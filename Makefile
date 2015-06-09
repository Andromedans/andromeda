OCAMLBUILD_FLAGS = -cflags -g,-annot,"-warn-error +a" -use-ocamlfind -pkg menhirLib -pkg sedlex
OCAMLBUILD_MENHIRFLAGS = -use-menhir -menhir "menhir --explain"
#OCAMLBUILD_MENHIRFLAGS = -use-menhir -menhir "menhir --explain --trace"

all: andromeda.byte
opt: andromeda.native
default: andromeda.byte
debug: andromeda.d.byte
profile: andromeda.p.native

andromeda.byte andromeda.native andromeda.d.byte andromeda.p.native: src/build.ml
	ocamlbuild -lib unix -lib str $(OCAMLBUILD_MENHIRFLAGS) $(OCAMLBUILD_FLAGS) $@

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
LIB_DIR ?= $(PREFIX)/lib
SHARE_DIR ?= $(PREFIX)/share
DOC_DIR := $(DOC_DIR)/andromeda
LIB_DIR := $(LIB_DIR)/andromeda
EXAMPLE_DIR := $(LIB_DIR)/examples

install: install-binary install-lib install-examples install-project-info install-emacs

install-binary: opt
	install -D _build/src/andromeda.native $(BIN_DIR)/andromeda

install-examples:
	install -d $(EXAMPLE_DIR)
	install -m644 examples/* $(EXAMPLE_DIR)

install-doc: doc
	install -d $(DOC_DIR)
	install -m 644 doc/theory.pdf $(DOC_DIR)/theory.pdf

install-project-info:
	install -d $(DOC_DIR)
	install -m 644 README.markdown $(DOC_DIR)/README.markdown
	install -m 644 CHANGELOG.md $(DOC_DIR)/CHANGELOG.md

emacs-autoloads:
	cd etc && emacs --batch --eval '(setq backup-inhibited t)' --eval '(update-file-autoloads "andromeda.el" t "'`pwd`'/andromeda-autoloads.el")'

install-emacs:
	install -d $(SHARE_DIR)/emacs/site-lisp
	install -m 644 etc/andromeda.el $(SHARE_DIR)/emacs/site-lisp
	install -m 644 etc/andromeda-autoloads.el $(SHARE_DIR)/emacs/site-lisp

install-lib:
	install -D -m 644 prelude.m31 $(LIB_DIR)/prelude.m31

uninstall:
	rm -f $(BIN_DIR)/andromeda \
 $(DOC_DIR)/andromeda-theory.pdf $(DOC_DIR)/CHANGELOG.md $(DOC_DIR)/README.markdown \
 $(LIB_DIR)/prelude.m31
	rm -f $(EXAMPLE_DIR)/* || true
	rmdir $(EXAMPLE_DIR) $(LIB_DIR) $(DOC_DIR) || true

version:
	@git describe --always --long

src/build.ml:
	/bin/echo -n 'let version = "' > $@
	$(MAKE) -s version | tr -d '\n' >> $@
	/bin/echo '" ;;' >> $@
	echo "let lib_dir = \""$(LIB_DIR)"\" ;;" >> $@


doc: default
	cd doc && latex -output-format pdf theory.tex
	/bin/mkdir -p ./doc/html
	ocamlbuild -docflag "-d" -docflag "doc/html" doc/andromeda.docdir/index.html

clean:
	ocamlbuild -clean

.PHONY: doc src/build.ml clean andromeda.byte andromeda.native version \
install install-binary install-doc install-examples install-lib uninstall
