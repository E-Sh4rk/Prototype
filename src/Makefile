
all: build run

build:
	dune build prototype.exe

run:
	dune exec ./prototype.exe

clean:
	dune clean

js:
	dune build prototype_js.bc.js
	cp _build/default/prototype_js.bc.js html/prototype_js.js
	