# Occurence Typing with Set-Theoretic Types prototype

## Compiling from scratch

The easiest way to install from scratch is through [opam](https://opam.ocaml.org/), the OCaml Package Manager.
It has been tested on OCaml 4.14.0.

Once `opam` is installed, CDuce needs to be installed before running this prototype.

### Installing CDuce

```
opam pin add cduce-types 'git+https://gitlab.math.univ-paris-diderot.fr/cduce/cduce#types-improvements'

opam pin add cduce 'git+https://gitlab.math.univ-paris-diderot.fr/cduce/cduce#types-improvements'

opam install cduce-types cduce
```

### Building the prototype

Once CDuce is installed, our prototype can be built using

```
git clone git@github.com:E-Sh4rk/Prototype.git
cd Prototype/src
opam install ppx_deriving ppx_inline_test ppx_expect menhir pomap
make
```

### Building the Javascript prototype

First, build the native prototype then :

```
make js
```

Then either serve the whole content of the [html/] directory through a Web server or open the file [index.html]
directly from a browser (**warning** : directly opening the file only works from Chrome/Chromium. Firefox will not
be able to load the prototype but not the example files due to the same-origin policy).


## Running the prototype

Once compiled, the prototype can be executed with (assuming the current directory is `Prototype/src`):
```
dune exec -- ./prototype.exe [file]
```
If no file is given, the file `test.ml` from the current path is used. The [html]() directory of the repository contains several example files. The syntax is given on the [webpage of the online prototype](https://typecaseunion.github.io/).
