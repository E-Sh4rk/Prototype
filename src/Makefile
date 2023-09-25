
all: build run

build:
	dune build main/prototype.exe

run:
	dune exec ./main/prototype.exe

clean:
	dune clean
	rm -f ../webeditor/typechecker.js

libjs:
	dune build --profile release main/lib_js.bc.js
	cp _build/default/main/lib_js.bc.js ../webeditor/typechecker.js
	chmod +w ../webeditor/typechecker.js

test:
	dune runtest

perf:
	sudo perf record --call-graph=dwarf -- ./_build/default/main/prototype.exe
	sudo perf report
