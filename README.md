# Prototype

## Installing OPAM

```
sudo apt install opam
opam init
eval `opam config env`
opam switch 4.07.1
eval `opam config env`
```

## Installing Cduce

```
git clone -b cduce-next git@gitlab.math.univ-paris-diderot.fr:cduce/cduce.git
cd cduce
sudo apt install m4
opam install num ulex
./configure --without-pxp --without-expat --without-netclient --without-netstring --without-cgi --without-curl --prefix=~/usr/local
make all
make install
cp lib/* ~/.opam/4.07.1/lib/cduce/
nano ~/.opam/4.07.1/lib/cduce/META
```

Remove occurences of `+camlp4/camlp4lib.cma` and `+camlp4/camlp4lib.cmxa`, and save.

## Building the prototype

```
git clone git@github.com:E-Sh4rk/Prototype.git
cd Prototype/src
opam install dune
eval $(opam env)
opam install ppx_deriving menhir
make
```

