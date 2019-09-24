BUILD_CMD=${BUILD_CMD:-make all}
## basic OCaml and opam installation

full_apt_version () {
  package=$1
  version=$2
  case "${version}" in
      latest) echo -n "${package}" ;;
      *) echo -n "${package}="
         apt-cache show $package \
             | sed -n "s/^Version: \(${version}\)/\1/p" \
             | head -1
  esac
}

set -uex

# the ocaml version to test
OCAML_VERSION=${OCAML_VERSION:-latest}

# the base opam repository to use for bootstrapping and catch-all namespace
BASE_REMOTE=${BASE_REMOTE:-git://github.com/ocaml/opam-repository}

# Add Anil's Ubuntu repo for Opam 2
ppa=avsm/ppa
sudo add-apt-repository --yes ppa:${ppa}
sudo apt-get update -qq
sudo apt-get install -y \
     $(full_apt_version ocaml $OCAML_VERSION) \
     $(full_apt_version ocaml-base $OCAML_VERSION) \
     $(full_apt_version ocaml-native-compilers $OCAML_VERSION) \
     $(full_apt_version ocaml-compiler-libs $OCAML_VERSION) \
     $(full_apt_version ocaml-interp $OCAML_VERSION) \
     $(full_apt_version ocaml-base-nox $OCAML_VERSION) \
     $(full_apt_version ocaml-nox $OCAML_VERSION) \
     $(full_apt_version camlp4 $OCAML_VERSION) \
     $(full_apt_version camlp4-extra $OCAML_VERSION) \
     $(full_apt_version opam latest)

ocaml -version
opam --version
export OPAMYES=1
# opam init -a ${BASE_REMOTE}
opam init
eval $(opam config env)
opam switch install 4.07.0
opam switch 4.07.0
eval $(opam config env)

# install Andromeda as recommended on the website ; pulls in dependencies
opam pin add andromeda .

# run
${BUILD_CMD}
