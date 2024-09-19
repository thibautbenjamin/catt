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

(package
  (name catt)
  (synopsis "An infinity-categorical coherence typechecker")
  (description "An infinity-categorical coherence typechecker")
  (depends ocaml dune)
  (tags
    (higher-categories dependent-type-theory)))