SOURCES = std.ml settings.ml common.ml syntax.ml gassoc.ml kernel.ml command.ml lexer.mll parser.mly prover.ml catt.ml
DOC_FILES = kernel.ml
RESULT = catt
ANNOTATE = true

all: dnc
# all: pnc
	  ./catt ../test/test.catt
	  ./catt ../test/functoriality.catt
	  ./catt ../examples/syllepsis.catt

web: web.ml dc
	ocamlfind $(OCAMLC) -package js_of_ocaml -package js_of_ocaml.syntax -syntax camlp4o -linkpkg -c  web.ml
	ocamlfind $(OCAMLC) -package js_of_ocaml -package js_of_ocaml.syntax -syntax camlp4o -linkpkg $(IMPL_CMO) web.cmo -o $(RESULT)
	js_of_ocaml $(RESULT)

include OCamlMakefile
