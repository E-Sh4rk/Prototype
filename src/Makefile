
all: build run

build:
	dune build prototype.exe

run:
	dune exec ./prototype.exe

clean:
	dune clean
	rm -f html/prototype_js.js

js:
	dune build --profile release prototype_js.bc.js
	cp _build/default/prototype_js.bc.js html/prototype_js.js
	chmod +w html/prototype_js.js

libjs:
	dune build --profile release lib_js.bc.js
	cp _build/default/lib_js.bc.js html/typechecker.js
	chmod +w html/typechecker.js

test:
	dune runtest

issues:
	cd main ; \
	dune exec ./issues.exe
