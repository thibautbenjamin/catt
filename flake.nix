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
          ocamlPackages = pkgs.ocaml-ng.ocamlPackages_4_14;
      in {
        packages = {
          default = self.packages.${system}.catt;

          catt = ocamlPackages.buildDunePackage {
            pname = "catt";
            version = "1.0";
            minimalOcamlVersion = "4.08";

            src = ./.;

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

        devShells.default = pkgs.mkShell {
          packages =
            (with pkgs;
              [  nixpkgs-fmt
                 fswatch ])
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
