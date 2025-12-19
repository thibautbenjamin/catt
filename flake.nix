{
  description = "An infinity-categorical coherence typechecker";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
    nix-filter.url = "github:numtide/nix-filter";
  };

  outputs = { self, nixpkgs, flake-utils, nix-filter, ... }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = (import nixpkgs { inherit system; });
        ocamlPackages = pkgs.ocaml-ng.ocamlPackages_4_14;
        sources = {
          catt = nix-filter.lib {
            root = ./src;
            include = [
              "dune-project"
              (nix-filter.lib.inDirectory "bin")
              (nix-filter.lib.inDirectory "lib")
              (nix-filter.lib.inDirectory "test.t")
            ];
          };

          coq-plugin = nix-filter.lib {
            root = ./.;
            include = [
              "dune-project"
              (nix-filter.lib.inDirectory "src/coq_plugin")
            ];
          };
        };

      in {
        packages = {
          default = self.packages.${system}.catt;

          catt = ocamlPackages.buildDunePackage {
            pname = "catt";
            version = "1.0";
            minimalOcamlVersion = "4.14";
            doCheck = false;

            src = sources.catt;

            nativeBuildInputs = with ocamlPackages; [ menhir ];

            propagatedBuildInputs = with ocamlPackages; [ base ];

            meta = {
              description = "A proof assistant for weak omega-categories";
              homepage = "";
              license = nixpkgs.lib.licenses.mit;
              maintainers = [ "Anonymized" ];
              mainProgram = "catt";
            };
          };

          catt-coq-plugin = pkgs.coqPackages.mkCoqDerivation {
            pname = "catt-plugin";
            version = "1.0";
            src = sources.coq-plugin;
            nativeBuildInputs = [ ];

            buildInputs =
              [ self.packages.${system}.catt pkgs.dune_3 pkgs.opam ];
            mlPlugin = true;
            useDune = true;

            meta = {
              description = "Coq plugin for the catt proof-assistant";
              homepage = "";
              license = nixpkgs.lib.licenses.mit;
              maintainers = [ "Anonymized" ];
            };
          };
        };

        formatter = pkgs.nixfmt-classic;

        devShells.default = pkgs.mkShell {
          inputsFrom = [
            self.packages.${system}.catt
            self.packages.${system}.catt-coq-plugin
          ];
        };
      });
}
