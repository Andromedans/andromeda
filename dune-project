(lang dune 3.12)
(name andromeda)
(version 2.0)
(using menhir 2.0)
(generate_opam_files)

(package
 (name "andromeda")
 (authors
  "Andrej Bauer"
  "Gaëtan Gilbert"
  "Philipp G. Haselwarter"
  "Christopher A. Stone")
 (maintainers
  "Philipp G. Haselwarter <philipp@haselwarter.org>"
  "Luna Strah <strah.luna@gmail.com>")
 (source (github Andromedans/andromeda))
 (bug_reports "https://github.com/Andromedans/andromeda/issues")
 (homepage "https://github.com/Andromedans/andromeda")
 (synopsis "¸¸.•*¨*• A Prover for Type Theories à la Martin-Löf •*¨*•.¸¸")
 (license "BSD-2-Clause")
 (depends (ocaml (>= 4.07.0)) dune dune-build-info menhir sedlex))
