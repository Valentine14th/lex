build:
	dune build

clean:
	dune clean

install-deps:
	opam install . --deps-only

install:
	dune build
	opam install .

mli:
	ocamlc -i src/*.ml
