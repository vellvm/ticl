default: build

build:
	$(MAKE) -C coinduction install
	dune build

clean:
	dune clean

doc:
	dune build @doc

depgraph::
	coqdep *.v -dumpgraph depgraph.dot 1>/dev/null 2>/dev/null
	sed -i 's/\[label=\"\([^"]*\)\"]/[label="\1";URL=".\/html\/TICL.\1.html"]/g' depgraph.dot
	dot depgraph.dot -Tpdf -o depgraph.pdf

.PHONY: build clean docs depgraph
