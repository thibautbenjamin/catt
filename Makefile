# Frontend to dune.

.PHONY: default build install uninstall test clean web

default: build

build:
	dune build

test:
	dune runtest -f

install:
	dune install

uninstall:
	dune uninstall

clean:
	dune clean
	rm -f pages/catt.js

web:
	dune build
	cp _build/default/web/web.bc.js pages/catt.js
