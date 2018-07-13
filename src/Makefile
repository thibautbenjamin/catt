SOURCES = stdlib.ml settings.ml common.ml kernel.ml lexer.mll parser.mly command.ml prover.ml catt.ml
DOC_FILES = kernel.ml
RESULT = catt
ANNOTATE = true

all: dnc
	# ./catt ../examples/sam.catt
	  ./catt ../examples/test.catt
	# ./catt ../examples/double-braiding-dim4.catt
	#./catt ../examples/syllepsis.catt

include OCamlMakefile
