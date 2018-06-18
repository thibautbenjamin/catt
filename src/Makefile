SOURCES = stdlib.ml settings.ml common.ml pShape.ml kernel.ml lexer.mll parser.mly macrosEnvironnement.ml unravel.ml command.ml prover.ml catt.ml
DOC_FILES = kernel.ml
RESULT = catt
ANNOTATE = true

all: dnc
	# ./catt ../examples/sam.catt
	./catt ../examples/double-braiding-dim4.catt

include OCamlMakefile
