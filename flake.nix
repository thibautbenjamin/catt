{
  description = "An infinity-categorical coherence typechecker";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
    nix-filter.url = "github:numtide/nix-filter";
  };

  outputs = { self, nixpkgs, flake-utils, nix-filter,... }:
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

            web = nix-filter.lib {
              root = ./.;
              include = [
                ".ocamlformat"
                "dune-project"
                (nix-filter.lib.inDirectory "web")
                (nix-filter.lib.inDirectory "lib")
              ];
            };

            nix = nix-filter.lib {
              root = ./.;
              include = [
                (nix-filter.lib.matchExt "nix")
              ];
            };

            elisp = ./share/site-lisp;
          };

      in {
        packages = {
          default = self.packages.${system}.catt;

          catt = ocamlPackages.buildDunePackage {
            pname = "catt-web";
            version = "1.0";
            minimalOcamlVersion = "4.08";
            doCheck = false;

            src = sources.ocaml;

            nativeBuildInputs = with ocamlPackages;
              [ menhir ];

            buildInputs = with ocamlPackages;
              [ fmt sedlex ];

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

          catt-web = ocamlPackages.buildDunePackage {
            pname = "catt";
            version = "1.0";
            minimalOcamlVersion = "4.08";
            doCheck = false;

            src = sources.web;

            nativeBuildInputs = with ocamlPackages;
              [ menhir
                js_of_ocaml ];

            buildInputs = with ocamlPackages;
              [ js_of_ocaml-ppx
                fmt
                sedlex ];

            propagatedBuildInputs = with ocamlPackages;
              [ base ];


            meta = {
              description = "Browser embedded version of the catt theorem prover";
              homepage = "https://www.github.com/thibautbenjamin/catt";
              license = nixpkgs.lib.licenses.mit;
              maintainers = [ "Thibaut Benjamin" "Chiara Sarti" ];
            };
          };

          catt-mode = pkgs.emacs.pkgs.trivialBuild rec {
            pname = "catt-mode";
            version = "v1.0.0";
            src = sources.elisp;

            meta = {
              description = "An emacs mode for the catt proof-assistant";
              homepage = "https://www.github.com/thibautbenjamin/catt";
              license = pkgs.lib.licenses.mit;
              maintainers = [ "Thibaut Benjamin" ];
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
            (with pkgs; [ nixpkgs-fmt fswatch ]) ++
            (with ocamlPackages;
              [ odoc
                ocaml-lsp
                ocamlformat
                ocp-indent
                ocamlformat-rpc-lib
                utop ]);

          inputsFrom = [ self.packages.${system}.catt
                         self.packages.${system}.catt-web ];
        };
      });
}
