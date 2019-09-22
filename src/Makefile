include ../Makefile.conf

all: minilucy.byte

parser.ml parser.mli: parser.mly
	menhir $^

lexer.ml: lexer.mll
	ocamllex $^

minilucy.byte: $(MLS)
	ocamlc -o $@ $^

clean:
	rm -f parser.ml parser.mli lexer.ml *.cmi *.cmo *.byte
