(lang dune 3.12)
(name andromeda)
(version 2.0)
(using menhir 2.0)
(using dune_site 0.1)
(generate_opam_files)

(package

 (name "andromeda")

 (authors
  "Andrej Bauer"
  "Gaëtan Gilbert"
  "Philipp G. Haselwarter"
  "Anja Petković Komel"
  "Christopher A. Stone")

 (maintainers
  "Andrej Bauer <andrej.bauer@andrej.com>"
  "Luna Strah <strah.luna@gmail.com>"
  "Philipp G. Haselwarter <philipp@haselwarter.org>")

 (source (github Andromedans/andromeda))

 (bug_reports "https://github.com/Andromedans/andromeda/issues")

 (homepage "https://www.andromeda-prover.org")

 (synopsis "A proof checker for user-definable dependent type theories")

 (license "BSD-2-Clause")

 (depends (ocaml (>= 4.12.0)) dune dune-build-info dune-site menhir sedlex))
