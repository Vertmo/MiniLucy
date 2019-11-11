include Makefile.conf

all: minilucy.byte samples

minilucy.byte: $(addprefix src/,$(SRC))
	make -C src minilucy.byte
	cp src/minilucy.byte .

samples: minilucy.byte
	make -C samples

rapport.pdf: rapport.tex
	pdflatex rapport.tex

clean:
	rm -f *.byte
	make -C src clean
	make -C samples clean
