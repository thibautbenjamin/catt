{
  description = "An infinity-categorical coherence typechecker";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
    flake-compat.url = "https://flakehub.com/f/edolstra/flake-compat/1.tar.gz";
    nix-filter.url = "github:numtide/nix-filter";
  };

  outputs = inputs@{ self, nixpkgs, flake-utils, nix-filter,... }:
    flake-utils.lib.eachDefaultSystem (system:
      let pkgs = (import nixpkgs { inherit system; });
          ocamlPackages = pkgs.ocaml-ng.ocamlPackages_4_14;
          sources = {
            ocaml = nix-filter.lib {
              root = ./.;
              include = [
                ".ocamlformat"
                "dune-project"
                (nix-filter.lib.inDirectory "bin")
                (nix-filter.lib.inDirectory "lib")
                (nix-filter.lib.inDirectory "test.t")
              ];
            };

            nix = nix-filter.lib {
              root = ./.;
              include = [
                (nix-filter.lib.matchExt "nix")
              ];
            };
          };

      in {
        packages = {
          default = self.packages.${system}.catt;

          catt = ocamlPackages.buildDunePackage {
            pname = "catt";
            version = "1.0";
            minimalOcamlVersion = "4.08";
            doCheck = false;

            src = sources.ocaml;

            nativeBuildInputs = with ocamlPackages;
              [ menhir
                js_of_ocaml
                js_of_ocaml-ppx ];

            buildInputs = with ocamlPackages;
              [
                js_of_ocaml
                js_of_ocaml-ppx
                fmt
                sedlex
              ];

            propagatedBuildInputs = with ocamlPackages;
              [ base ];


            meta = {
              description = "A proof assistant for weak omega-categories";
              homepage = "https://www.github.com/thibautbenjamin/catt";
              license = nixpkgs.lib.licenses.mit;
              maintainers = [ "Thibaut Benjamin" "Chiara Sarti" ];
              mainProgram = "catt";
            };
          };
        };

        checks = {
          default = self.packages.${system}.catt.overrideAttrs
            (oldAttrs: {
              name = "check-${oldAttrs.name}";
              dontInstall = true;
              doCheck = true;
            });
        };

        devShells.default = pkgs.mkShell {
          packages =
            (with pkgs; [  nixpkgs-fmt fswatch ])
            ++
            (with ocamlPackages;
              [ odoc
                ocaml-lsp
                ocamlformat
                ocp-indent
                ocamlformat-rpc-lib
                utop ]);

          inputsFrom = [ self.packages.${system}.catt ];
        };
      });
}
