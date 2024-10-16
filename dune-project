(lang dune 3.15)
(using coq 0.6)
(name coq-ictl)

(license "MIT")
(authors "Eleftherios Ioannidis" "Yannick Zakowski" "Paul He")
(maintainers "Eleftherios Ioannidis")
(source (github vellvm/ictl))
(bug_reports "https://github.com/vellvm/ictl/issues")

(generate_opam_files true)

(package
 (name coq-ictl)
 (synopsis "Library for structural temporal logic proofs over coinductive, free monads with effects and choice.")
 (version 0.1)
 (depends
  (coq (>= 8.17))
  (coq-ext-lib (>= 0.11.3))
  (coq-coinduction (>= 1.3))
  (coq-relation-algebra (>= 1.7))
  (coq-equations (>= 1.2))
 )
)
