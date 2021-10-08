# Occurence Typing with Set-Theoretic Types prototype

## Installing
### Online prototype

An **online prototype** is available [here](https://typecaseunion.github.io/) to test the prototype directly in the browser (we recommend using Firefox).

### Virtual Machine Image

An Debian based virtual machine image with the pre-installed prototype is available [here](https://www.lri.fr/~kn/files/TypecaseUnion.ova). The VM starts a graphical user session (LXDE) with a two icons, a `README.txt` file and `LXTerminal` shortcut. The terminal can be used to access the `Prototype` directory containing the code, already built. You can then [run the prototype](#running-the-prototype).


### Dockerfile

A minimal container can be built from the [Dockerfile]() present in the repository. An image can be build with (assuming the Dockerfile is in the current repository)
:
```
docker build --no-cache -t occtyping .
```
Once the image is build, start the container with :
```
docker run -ti --rm occtyping
```
The `Prototype` directory contains the source code of the  prototype, already built. You can then  [run the prototype](#running-the-prototype).


## Compiling from scratch

The easiest way to install from scratch is through [opam](https://opam.ocaml.org/), the OCaml Package Manager.
The prototype supports OCaml version 4.07.1 to 4.13.1.

Once `opam` is installed, CDuce needs to be installed before the prototype.

### Installing CDuce

```
opam pin add cduce-types 'git+https://gitlab.math.univ-paris-diderot.fr/cduce/cduce#polymorphic'

opam pin add cduce 'git+https://gitlab.math.univ-paris-diderot.fr/cduce/cduce#polymorphic'

opam install cduce-types cduce

```
In the unlikely event that the main server is down, an alternative URL can be used:
```
opam pin add cduce-types 'git+https://www.lri.fr/~kn/mirror/cduce.git#polymorphic'

opam pin add cduce 'git+https://www.lri.fr/~kn/mirror/cduce.git#polymorphic'

opam install cduce-types cduce

```


### Building the prototype
Once CDuce is installed, the prototype can be built using

```
git clone git@github.com:E-Sh4rk/Prototype.git
git checkout -b popl22-AE origin/popl22-AE
cd Prototype/src
opam install dune
eval $(opam env)
opam install ppx_deriving menhir pomap
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
