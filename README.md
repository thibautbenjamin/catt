Artifacts for FSCD submission Generating Higher Identity Proofs in Homotopy Type Theory
========================================================================================

# Proof artifacts

All proof artefacts produced by running catt, coq 8.20 and the catt plugin for coq, are located in the  the directory `artefacts/`. The source files are located in the `experiment/` directory.

# Build Instructions

## Install dependencies

### Using opam (recommended)
Make sure that [opam](https://opam.ocaml.org/doc/Install.html) is installed and initialised on your system. We will create a local opam switch in this directory with all the dependencies required to build catt. For reproducibility, a file is provided with the exact version of those depencies. To create the switch, move to the root of this directory and run the following commands
```shell
opam switch create ./ --empty
opam repo add coq-released https://coq.inria.fr/opam/released
opam switch import dependencies.export
eval $(opam env)
```
**Warning**: On windows, we recommend that those commands are run within the Windows Subsystem for Linux.
**Warning**: If you exit and re-enter this directory, make sure to run `eval $(opam env)` before doing anything else.

### Using nix
Alternatively, the dependencies can be built with nix, using the provided flake. For reproducibility, a lock file is also provided. To build Catt together with the coq plugin with nix, ensure that nix is installed on your system and run the following commands from within the artifacts directory
```shell
nix develop
```

## Build Catt
After following the instruction to install the dependencies, simply the following command to build Catt.
```shell
dune build
```
**Warning**: The compilation may complain about a `Dynlink` error. This error concerns the Coq plugin, and is resolved by running `dune build` again.

# Usage

## Illustration with the tutorial
Usage of catt is illustrated with the file `examples/tutorial.catt`. To run Catt on the file, navigate to the directory `examples` and execute the command
```shell
dune exec -- catt base.catt
```
**Warning**: Make sure that you open the editor from the terminal pointing at this directory, for your editor to see the correct version of coq that was installed during the first phase.

The file `examples/syntax.catt` gives a demonstration of advanced use of the syntax of catt

## Experiment and helper script
The directory `experiment/` contains a subset of source files that we have used to produce our proof artifacts. It also contains a script `run-experiment.sh` that executes on all files in the subdirectory and stores the result in a subdirectory `results/`.