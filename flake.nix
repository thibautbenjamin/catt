{
  description = "An infinity-categorical coherence typechecker";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
    coq-hott.url = "github:HoTT/Coq-HoTT";
  };

  outputs = inputs@{ nixpkgs, flake-utils,  ... }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = (import nixpkgs { inherit system; });
        ocamlPackages = pkgs.ocaml-ng.ocamlPackages_4_14;
      in {

        devShells.default = pkgs.mkShell {
          packages = (with pkgs; [
            nixfmt-classic
            fswatch
            dune_3
            opam
            coq
          ])
          ++ (with ocamlPackages; [
            ocaml
            menhir
            base
            ocaml-lsp
            ocamlformat
            ocamlformat-rpc-lib
            utop
          ]) ++ [ inputs.coq-hott.packages.${system}.default ];
        };
      });
}
