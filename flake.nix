{
  description = "An infinity-categorical coherence typechecker";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
    flake-compat.url = "https://flakehub.com/f/edolstra/flake-compat/1.tar.gz";
  };

  outputs = inputs@{ self, nixpkgs, flake-utils, ... }:
    flake-utils.lib.eachDefaultSystem (system:
      let pkgs = (import nixpkgs { inherit system; });
      in {
        # Exports a package that can be built with
        # nix built. The build environment can be accessed
        # via nix develop.
        packages = rec {
          default = self.packages.${system}.catt;
          catt = pkgs.callPackage
            ({ stdenv, dune_3, ocaml, opam, ocamlPackages, ... }:
              stdenv.mkDerivation {
                pname = "catt";
                version = "0.2.0";
                src = ./.;
                buildInputs = [ dune_3 ocaml opam ] ++ (with ocamlPackages; [
                  fmt
                  js_of_ocaml
                  js_of_ocaml-ppx
                  menhir
                  sedlex
                ]);
                buildPhase = ''
                  rm -rf result
                  dune build
                '';
                installPhase = ''
                  mkdir -p $out/bin
                  install -Dm755 _build/default/bin/catt.exe $out/bin
                  mkdir -p $out/web
                  #install -Dm644 _build/default/web/index.html $out/web
                  #install -Dm644 _build/default/web/*.js $out/web
                '';
              }) { };
        };
      });
}
