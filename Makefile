include Makefile.conf

all: minilucy.byte samples

minilucy.byte: $(addprefix src/,$(SRC))
	make -C src minilucy.byte
	cp src/minilucy.byte .

samples: minilucy.byte
	make -C samples

clean:
	rm -f *.byte
	make -C src clean
	make -C samples clean
