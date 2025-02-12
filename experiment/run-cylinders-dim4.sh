#!/bin/sh

coqc -R ../_build/default/src/coq_plugin/theories/ Catt -I ../_build/install/default/lib/ cylinders/Compdim4.v

coqc -R ../_build/default/src/coq_plugin/theories/ Catt -I ../_build/install/default/lib/ cylinders/Stackdim4.v
