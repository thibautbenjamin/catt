(lang dune 3.7)

(name catt)

(generate_opam_files true)

(source
  (github thibautbenjamin/catt))

(authors "Thibaut Benjamin")

(maintainers "Thibaut Benjamin")

(license MIT)

(using menhir 2.0)

(package
  (name catt)
  (synopsis "An infinity-categorical coherence typechecker")
  (description "An infinity-categorical coherence typechecker")
  (depends ocaml dune)
  (tags
    (higher-categories dependent-type-theory)))