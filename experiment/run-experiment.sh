#!/bin/sh

coqc -noinit -indices-matter eckmann-hilton/EHHoTT.v | sed -n '/^[  \t]*:/q;p' | sed 's/^[ \t]*//' > results/eh-from-hott
HOTT_TERM=$(wc -c results/eh-from-hott | sed 's/ .*//')
printf "term from the hott library: $HOTT_TERM characters, saved in file results/eh-from-hott\n\n"

coqc -noinit -indices-matter eckmann-hilton/EHChristensen.v | sed -n '/^[  \t]*:/q;p' | sed 's/^[ \t]*//' > results/eh-hott-christensen
CHR_TERM=$(wc -c results/eh-hott-christensen | sed 's/ .*//')
CHR_SRC=$(wc -c eckmann-hilton/EHChristensen.v | sed 's/ .*//')
printf "term from hott using Christensen's proof: $CHR_TERM characters, saved in file eh-hott-christensen\n"
printf "length of the coq file containing Christensen's proof: $CHR_SRC characters\n\n"

coqc -R ../_build/default/coq_plugin/theories/ Catt -I ../_build/install/default/lib/ eckmann-hilton/EHCaTT.v | sed -n '/^[  \t]*:/q;p' | sed '/\[=\^\.\^=\]\|\[=I\.I=\]/d' | sed 's/^[ \t]*//' > results/eh-from-catt
CATT_TERM=$(wc -c results/eh-from-catt | sed 's/ .*//')
CATT_SRC=$(wc -c eckmann-hilton/eh.catt | sed 's/ .*//')
printf "term from catt export: $CATT_TERM characters, saved in file eh-from-catt\n"
printf "length of the catt file defining eckmann-hilton: $CATT_SRC characters"

printf "term from the hott library: $HOTT_TERM characters \n\n term from hott using Christensen's proof: $CHR_TERM characters \n length of the coq file containing Christensen's proof: $CHR_SRC characters \n\n term from catt export: $CATT_TERM characters \n length of the catt file defining eckmann-hilton: $CATT_SRC characters" > results/counts
