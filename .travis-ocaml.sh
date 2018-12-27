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
# BASE_REMOTE=${BASE_REMOTE:-git://github.com/ocaml/opam-repository}

case "$OCAML_VERSION" in
    3.12) ppa=avsm/ocaml312+opam12 ;;
    4.00) ppa=avsm/ocaml40+opam12  ;;
    4.01) ppa=avsm/ocaml41+opam12  ;;
    4.02) ppa=avsm/ocaml42+opam12  ;;
    latest) ppa=avsm/ppa-opam-experimental;;
    *)    echo Unknown compiler version; exit 1;;
esac

# sudo add-apt-repository \
#      "deb mirror://mirrors.ubuntu.com/mirrors.txt trusty main restricted universe"
# sudo add-apt-repository --yes ppa:${ppa}
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

opam init
eval $(opam config env)
opam install opam-depext

# install andromeda dependencies
! [ -z "$M31_DEPS" ] && opam install $M31_DEPS

# run
${BUILD_CMD}
