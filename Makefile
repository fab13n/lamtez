.PHONY: all clean byte native profile debug sanity test

OCB_FLAGS=-use-ocamlfind -use-menhir -I src -I lib
OCB=ocamlbuild $(OCB_FLAGS)

all: debug # byte native # profile debug

clean:
	$(OCB) -clean

native: sanity
	$(OCB) main.native

byte: sanity
	$(OCB) main.byte

profile: sanity
	$(OCB) -tag profile main.native

debug: sanity
	$(OCB) -tag debug main.d.byte

# check that menhir is installed, use "opam install menhir"
sanity:
	which menhir

test: native
	./main.native '\x: x+1'
