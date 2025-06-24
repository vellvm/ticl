(lang dune 3.15)
(using coq 0.8)
(name coq-ticl)
(warnings (deprecated_coq_lang_lt_08 disabled))

(license "MIT")
(authors "Eleftherios Ioannidis" "Yannick Zakowski" "Paul He")
(maintainers "Eleftherios Ioannidis")
(source (github vellvm/ticl))
(bug_reports "https://github.com/vellvm/ticl/issues")

(generate_opam_files true)

(package
 (name coq-ticl)
 (synopsis "Library for structural temporal logic proofs over coinductive trees.")
 (version 0.1)
 (depends
  (coq (>= 9.0))
  (rocq-ext-lib (>= 0.11.3))
  (coq-coinduction (>= 1.3))
  (coq-equations (>= 1.2))
 )
)
