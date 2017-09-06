.PHONY: all clean byte native profile debug sanity test

OCB_FLAGS=-use-ocamlfind -use-menhir -I src -pkgs str
OCB=ocamlbuild $(OCB_FLAGS)
COLORIZE=(ack 'File "[^"]+", line [0-9]+, characters [0-9]+-[0-9]+:' --passthru --color || true)



all: debug # byte native # profile debug

clean:
	$(OCB) -clean

native: sanity
	$(OCB) main.native | $(COLORIZE)

byte: sanity
	$(OCB) main.byte | $(COLORIZE)

profile: sanity
	$(OCB) -tag profile main.native

debug: sanity
	$(OCB) -tag debug main.d.byte | $(COLORIZE)

# check that menhir is installed, use "opam install menhir"
sanity:
	which menhir

test: debug native
	./tests/run-tests.sh

test-contracts: debug native
	./tests/run-tests.sh contracts
