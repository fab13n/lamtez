.PHONY: all clean native debug sanity test profile test-contracts main.native main.d.byte

COLORIZE=|(ack 'File "[^"]+", line [0-9]+, characters [0-9]+-[0-9]+:' --passthru --color || true)
# COLORIZE=
OCB_FLAGS=-use-ocamlfind -use-menhir -I src -pkgs str -pkgs unix
OCB=ocamlbuild $(OCB_FLAGS)
SHELLFLAGS=-o pipefail

all: native debug
debug: lamtez.d
native: lamtez

lamtez.d: main.d.byte
	cp $< $@

lamtez: main.native
	cp $< $@

clean:
	$(OCB) -clean
	$(RM) *.aux *.log

main.native:
	$(OCB) $@ $(COLORIZE)

profile: sanity
	$(OCB) -tag profile main.native

main.d.byte:
	$(OCB) -tag debug $@ $(COLORIZE)

# check that menhir is installed, use "opam install menhir"
sanity:
	which menhir

test: debug native
	mkdir -p michelson
	./test/run-tests.sh

test-contracts: debug native
	./test/run-tests.sh contracts
