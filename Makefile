include Makefile.conf

all: minilucy.byte

minilucy.byte: $(addprefix src/,$(SRC))
	make -C src minilucy.byte
	cp src/minilucy.byte .

clean:
	rm -f *.byte
	make -C src clean
