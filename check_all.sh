#!/bin/bash

TESTS=(
"test/bug.catt"
"test/builtin-comp.catt"
"test/functorialisation.catt"
"test/functoriality.catt"
"test/implicit_subs.catt"
"test/inverses.catt"
"test/issue7.catt"
"test/naturality.catt"
"test/opposites.catt"
"test/pretty-print.catt"
"test/ps-syntax.catt"
"test/suspension.catt"
"test/test.catt"
"test/vanilla.catt"
"test/wildcards.catt"
)

for file in ${TESTS[@]}; do
  echo "Running: $file"
  opam exec -- dune exec -- catt "$file" || exit 1
done

