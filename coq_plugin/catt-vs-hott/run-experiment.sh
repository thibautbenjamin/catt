#!/bin/sh

coqc -noinit -indices-matter EHHoTT.v | sed -n '/^[  \t]*:/q;p' > eh-from-hott
echo "term from the hott library: $(wc -c eh-from-hott | sed 's/ .*//') characters, saved in file eh-from-hott"

echo "length of the catt file defining eckmann-hilton: $(wc -c eh.catt | sed 's/ .*//') characters"

coqc -R ../../_build/default/coq_plugin/theories/ Catt -I ../../_build/install/default/lib/ EHCaTT.v | sed -n '/^[  \t]*:/q;p' | sed '/\[=\^\.\^=\]\|\[=I\.I=\]/d' > eh-from-catt
echo "term from the hott library: $(wc -c eh-from-catt | sed 's/ .*//') characters, saved in file eh-from-catt"
