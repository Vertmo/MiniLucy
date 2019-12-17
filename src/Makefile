include ../Makefile.conf

PWD = $(shell pwd)

all: minilucy.byte

config.ml:
	$(shell echo "let libdir = \"$(PWD)\"" > config.ml)

parser.ml parser.mli: parser.mly
	menhir $^

lexer.ml: lexer.mll
	ocamllex $^

minilucy.byte: $(MLS)
	ocamlc -o $@ $^

clean:
	rm -f parser.ml parser.mli lexer.ml config.ml *.cmi *.cmo *.byte *.o
