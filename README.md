# Prototype: Polymorphic Type Inference for Dynamic Languages

[![DOI](https://zenodo.org/badge/308046842.svg)](https://zenodo.org/badge/latestdoi/308046842)

The web version of this prototype can be tested [here](https://www.cduce.org/dynlang/) (or [there](https://e-sh4rk.github.io/Prototype/) for a more experimental version).

## Using the docker image

For convenience, a [Dockerfile](Dockerfile) is provided. Assuming the current directory contains the `Dockerfile`, the image can be built with:
```
docker build -t poly --rm .
```
Building the image takes about 10 minutes (depending on your connection speed and machine configuration). The
resulting image takes about 2.5GB. Once the image is built, it is recommended to launch the container
as such:
```
docker run --rm -p 9090:9090 --name poly_container poly
```
This exposes the Web version of the prototype on http://localhost:9090. The native version can
be used from within the container. To start a shell inside the running container, do:
```
docker exec -ti poly_container bash
```
You can then follow the instructions in the [Running the prototype](#running-the-prototype) section below. Within the container, the text editors `nano`, `vim` and `emacs` are available.

## Building the native version

First, clone and open this repository by doing
```
git clone git@github.com:E-Sh4rk/Prototype.git
cd Prototype/src
```

The easiest way to build the native version is through [opam](https://opam.ocaml.org/), the OCaml Package Manager.
This prototype has been tested on OCaml 4.14.1, that can be installed, together with
the dependencies, by doing the following (answer 'yes' when asked):
```
opam switch create dynlang_tc 4.14.1
eval $(opam env --switch=dynlang_tc)
make deps
```

Then, the prototype can be built using
```
make build
```

## Running the prototype

### Language syntax
The syntax of the language is described in the [online
help](https://e-sh4rk.github.io/Prototype/doc.html).

### Native version
Once compiled, the prototype can be executed from the `src` directory with
```
make run
```
or alternatively
```
dune exec -- ./main/prototype.exe [file]
```
If no file is given, the file `test.ml` from the current path is used.

### Javascript version (web editor)

You will need [npm](https://www.npmjs.com/) to install the dependencies of the Javascript version.
First, build the native version, then:
```
make libjs
cd ../webeditor
npm ci
```

Then either serve the whole content of the `./webeditor/` directory through a Web server or open the file `./webeditor/index.html` directly from a browser (**warning** : the later will not allow you to load the examples nor benefit from web-workers due to security policies).

## Hacking the sources

The main concepts of the paper *Polymorphic Type Inference for Dynamic Languages* are implemented in the `src/system` directory, where one can find the implementation of MSC-forms, the algorithmic typechecking system, and the reconstruction and reconstruction auxiliary type inference systems.

This software is distributed under the terms contained in the [LICENSE](LICENSE) file.