BUILD_CMD=${BUILD_CMD:-make all}

set -uex

# Add Anil's Ubuntu repo for Opam 2
ppa=avsm/ppa
sudo add-apt-repository --yes ppa:${ppa}
sudo apt-get update -qq
# Install Ocaml & Opam
sudo apt-get install -y ocaml opam
ocaml -version
opam --version
# Set up Opam
export OPAMYES=1
opam init
eval $(opam config env)
# Install a recent OCaml
opam switch install 4.07.0
opam switch 4.07.0
eval $(opam config env)

# install Andromeda as recommended on the website ; pulls in dependencies
opam pin add andromeda-1 .

# run
${BUILD_CMD}
