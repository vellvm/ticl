(lang dune 3.21)
(using rocq 0.11)
(name rocq-ticl)

(license "MIT")
(authors "Eleftherios Ioannidis" "Yannick Zakowski" "Paul He")
(maintainers "Eleftherios Ioannidis")
(source (github vellvm/ticl))
(bug_reports "https://github.com/vellvm/ticl/issues")

(generate_opam_files true)

(package
 (name rocq-ticl)
 (synopsis "Library for structural temporal logic proofs over coinductive trees.")
 (version 0.1)
 (depends
  (rocq-prover (>= 9.0))
  (coq-ext-lib (>= 0.11.3))
  (rocq-coinduction (>= 1.3))
  (rocq-equations (>= 1.3))
 )
)
