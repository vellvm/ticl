default: build

build:
	dune build

install: build
	dune build -p coq-ticl @install
	dune install

clean:
	dune clean

doc:
	dune build @doc
	cp docs/main.html _build/default/main.html

.PHONY: build clean doc
