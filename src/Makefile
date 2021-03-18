include ../Makefile.conf

PWD = $(shell pwd)

all: minilucy.native

config.ml:
	$(shell echo "let libdir = \"$(PWD)\"" > config.ml)

parser.ml parser.mli: parser.mly
	menhir $^

lexer.ml: lexer.mll
	ocamllex $^

minilucy.native: $(MLS)
	ocamlopt -o $@ $^

minilucy.cma: $(MLS_PRE) parser.mli parser.ml lexer.ml
	ocamlc -o $@ -a $^

clean:
	rm -f parser.ml parser.mli lexer.ml config.ml *.cmi *.cmo *.cma *.native *.o
