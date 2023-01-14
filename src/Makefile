
all: build run

build:
	dune build prototype.exe

run:
	dune exec ./prototype.exe

clean:
	dune clean
	rm -f html/prototype_js.js

libjs:
	dune build --profile release lib_js.bc.js
	cp _build/default/lib_js.bc.js webeditor/typechecker.js
	chmod +w webeditor/typechecker.js

test:
	dune runtest

issues:
	cd main ; \
	dune exec ./issues.exe
