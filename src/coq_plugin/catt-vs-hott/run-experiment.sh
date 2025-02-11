#!/bin/sh

coqc -noinit -indices-matter EHHoTT.v | sed -n '/^[  \t]*:/q;p' | sed 's/^[ \t]*//' > eh-from-hott
echo "term from the hott library: $(wc -c eh-from-hott | sed 's/ .*//') characters, saved in file eh-from-hott"

coqc -noinit -indices-matter EHChristensen.v | sed -n '/^[  \t]*:/q;p' | sed 's/^[ \t]*//' > eh-hott-christensen
echo "term from hott using Christensen's proof: $(wc -c eh-hott-christensen | sed 's/ .*//') characters, saved in file eh-hott-christensen"

echo "length of the catt file defining eckmann-hilton: $(wc -c eh.catt | sed 's/ .*//') characters"

coqc -R ../../_build/default/coq_plugin/theories/ Catt -I ../../_build/install/default/lib/ EHCaTT.v | sed -n '/^[  \t]*:/q;p' | sed '/\[=\^\.\^=\]\|\[=I\.I=\]/d' | sed 's/^[ \t]*//' > eh-from-catt
echo "term from catt export: $(wc -c eh-from-catt | sed 's/ .*//') characters, saved in file eh-from-catt"
