#warnings disabled:
# 4: fragile pattern matching (we try to stick to it but don't always)
#27: innocuous unused variable
#29: non-escaped end-of-line in string constant
#48: implicit elimination of optional arguments
#50: unexpected documentation comment
OCAMLBUILD_FLAGS = -cflags -g,-annot,"-warn-error +a",-w,+a-4-27-29-48-50 -use-ocamlfind -pkg menhirLib -pkg sedlex
OCAMLBUILD_MENHIRFLAGS = -use-menhir -menhir "menhir --explain"
#OCAMLBUILD_MENHIRFLAGS = -use-menhir -menhir "menhir --explain --trace"

all: andromeda.native
opt: andromeda.native
default: andromeda.native
byte: andromeda.byte
debug: andromeda.d.byte
profile: andromeda.p.native

andromeda.byte andromeda.native andromeda.d.byte andromeda.p.native: src/build.ml
	ocamlbuild -j 4 -lib unix $(OCAMLBUILD_MENHIRFLAGS) $(OCAMLBUILD_FLAGS) $@

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

version:
	@git describe --always --long

src/build.ml:
	/bin/echo -n 'let version = "' > $@
	$(MAKE) -s version | tr -d '\n' >> $@
	/bin/echo '" ;;' >> $@
	echo "let lib_dir = \""$(LIB_DIR)"\" ;;" >> $@

emacs-autoloads:
	cd etc && emacs --batch --eval '(setq backup-inhibited t)' --eval '(update-file-autoloads "andromeda.el" t "'`pwd`'/andromeda-autoloads.el")'

doc: default
	cd doc && latex -output-format pdf theory.tex
	/bin/mkdir -p ./doc/html
	ocamlbuild -docflag "-d" -docflag "doc/html" doc/andromeda.docdir/index.html



install: install-binary install-lib install-examples install-project-info install-emacs
uninstall: uninstall-binary uninstall-lib uninstall-examples uninstall-project-info uninstall-emacs

install-binary: opt
	install -d $(BIN_DIR)
	install _build/src/andromeda.native $(BIN_DIR)/andromeda
uninstall-binary:
	rm -f $(BIN_DIR)/andromeda

install-doc: doc
	install -d $(DOC_DIR)
	install -m 644 doc/theory.pdf $(DOC_DIR)/theory.pdf
uninstall-doc:
	rm -f $(DOC_DIR)/andromeda-theory.pdf
	rmdir $(DOC_DIR) || true

install-project-info:
	install -d $(DOC_DIR)
	install -m 644 README.markdown $(DOC_DIR)/README.markdown
	install -m 644 CHANGELOG.md $(DOC_DIR)/CHANGELOG.md
uninstall-project-info:
	rm -f $(DOC_DIR)/CHANGELOG.md $(DOC_DIR)/README.markdown
	rmdir $(DOC_DIR) || true

install-emacs:
	install -d $(SHARE_DIR)/emacs/site-lisp
	install -m 644 etc/andromeda.el $(SHARE_DIR)/emacs/site-lisp
	install -m 644 etc/andromeda-autoloads.el $(SHARE_DIR)/emacs/site-lisp
uninstall-emacs:
	rm -f $(SHARE_DIR)/emacs/site-lisp/andromeda.el $(SHARE_DIR)/emacs/site-lisp/andromeda-autoloads.el

install-lib:
	install -d $(LIB_DIR)
	install -m 644 prelude.m31 $(LIB_DIR)/prelude.m31
uninstall-lib:
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
install install-binary install-doc install-examples install-lib uninstall
