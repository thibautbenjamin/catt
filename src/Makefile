SOURCES = stdlib.ml settings.ml common.ml syntax.ml gassoc.ml kernel.ml lexer.mll parser.mly command.ml prover.ml catt.ml
DOC_FILES = kernel.ml
RESULT = catt
ANNOTATE = true

all: dnc
# all: pnc
	# ./catt ../examples/sam.catt
	  ./catt ../test/test.catt
	  ./catt ../test/functoriality.catt
	# ./catt ../examples/double-braiding-dim4.catt
	  ./catt ../examples/syllepsis.catt

web: web.ml dc
	$(OCAMLC) -annot -I `ocamlfind query js_of_ocaml` -pp "camlp4o -I `ocamlfind query js_of_ocaml` pa_js.cmo" -c web.ml
	$(OCAMLC) -I `ocamlfind query js_of_ocaml` js_of_ocaml.cma $(IMPL_CMO) web.cmo -o $(RESULT)
	js_of_ocaml $(RESULT)


include OCamlMakefile
