# Prototype

## Installing OPAM

```
sudo apt install opam
opam init
eval `opam config env`
opam switch 4.11.2
eval `opam config env`
```

## Installing Cduce

```
sudo apt install m4
opam pin add cduce-types 'git+https://gitlab.math.univ-paris-diderot.fr/cduce/cduce#polymorphic'
opam pin add cduce 'git+https://gitlab.math.univ-paris-diderot.fr/cduce/cduce#polymorphic'
```

## Building the prototype

```
git clone git@github.com:E-Sh4rk/Prototype.git
cd Prototype/src
opam install dune
eval $(opam env)
opam install ppx_deriving menhir pomap
make
```

