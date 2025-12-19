#!/bin/sh

resfile="./results/all_sizes"

mkdir -p ./results
find ./results -type f -delete

for filename in *.catt; do
    [ -f "$filename" ] || break
    fileres="./results/${filename%.catt}"
    echo "Benchmarking file $filename ..."
    dune exec -- catt $filename > $fileres
    sed -i '1d' $fileres
    wc -lc $fileres >> $resfile
done
