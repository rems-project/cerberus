(lang dune 2.0)
(name cerberus)

(using menhir 1.0)

(generate_opam_files true)

(source (github rems-project/cerberus-private))
(license "FIXME")
(authors "FIXME" "FIXME")
(maintainers "FIXME")

(package
 (name cerberus)
 (synopsis "The Cerberus C semantics")
 (description "The Cerberus C semantics and related tools.")
 (depends
  (angstrom (>= 0.13.0))
  (apron (>= v0.9.12))
  (cmdliner (>= 1.0.4))
  (cohttp-lwt-unix (>= 2.5.1))
  (dune (>= 2.0))
  (ezgzip (>= 0.2.3))
  (lem (= 2020-01-30))
  (lwt (>= 5.2.0))
  (pprint (>= 20180528))
  (ppx_sexp_conv (>= v0.13.0))
  (sexplib (>= v0.13.0))
  (sha (>= 1.12))
  (yojson (>= 1.7.0))
  (z3 (= 4.8.4)))
 (depopts
  (earley (= 2.0.0))))
