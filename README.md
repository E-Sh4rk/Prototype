# Set-Theoretic and Polymorphic Type System Prototype

The web version of this prototype can be tested [here](https://e-sh4rk.github.io/Prototype/).

## Native version

The easiest way to build the native version is through [opam](https://opam.ocaml.org/), the OCaml Package Manager.
This prototype has been tested on OCaml 4.14.1, that can be installed by doing `opam switch create 4.14.1`.

### Installing CDuce

The main dependency is the CDuce library. It can be installed this way:

```
opam pin add cduce-types 'git+https://gitlab.math.univ-paris-diderot.fr/cduce/cduce#dev'
opam pin add cduce 'git+https://gitlab.math.univ-paris-diderot.fr/cduce/cduce#dev'
```

### Building the prototype

Once CDuce is installed, our prototype can be built using

```
git clone git@github.com:E-Sh4rk/Prototype.git
cd Prototype/src
opam install ppx_inline_test ppx_expect ppx_deriving pomap
make
```

### Running the prototype

Once compiled, the prototype can be executed with `dune exec -- ./prototype.exe [file]`.
If no file is given, the file `test.ml` from the current path is used.

## Javascript version (web editor)

You will need [npm](https://www.npmjs.com/) to install the dependencies of the Javascript version.
First, build the native version, then:

```
opam install yojson js_of_ocaml-ppx
make libjs
cd ../webeditor
npm ci
```

Then either serve the whole content of the `./webeditor/` directory through a Web server or open the file `./webeditor/index.html` directly from a browser (**warning** : the later will not allow you to load the examples nor benefit from web-workers due to security policies).
