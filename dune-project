(lang dune 3.16)

(name catt)
(generate_opam_files true)
(source (github thibautbenjamin/catt))
(authors "Thibaut Benjamin"
         "Chiara Sarti")
(maintainers "Thibaut Benjamin"
             "Chiara Sarti")
(license MIT)
(using menhir 2.0)
(cram enable)
(using coq 0.9)

(package
  (name catt)
  (synopsis "An infinity-categorical coherence typechecker")
  (description "An infinity-categorical coherence typechecker")
  (depends
      (ocaml (and (>= 4.14) (< 5.0)))
      (dune (>= 3.10))
      (menhir (>= 20240715))
      (base (>= 0.17.0))
      (landmarks (>= 1.4))
      (landmarks-ppx (>= 1.4)))
  (tags
    (higher-categories dependent-type-theory)))

(package
  (name coq-catt-plugin)
  (synopsis "A Coq plugin for the catt proof-assistant")
  (description "A Coq plugin to interpret terms built in the catt proof assistant as functions computing on higher dimensional identity types")
  (depends
      catt
      (coq (>= 8.20)))
  (tags
    (higher-categories dependent-type-theory)))

(package
  (name catt-web)
  (synopsis "Browser embedded version of the catt theorem prover")
  (description "Browser embedded version of the catt theorem prover")
  (allow_empty)
  (tags
    (higher-categories dependent-type-theory)))
