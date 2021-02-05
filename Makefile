include Makefile.conf

all: minilucy.native src/avrlib.o src/liquidCrystal.o

src/config.ml:
	make -C src config.ml

minilucy.native: $(addprefix src/,$(SRC))
	make -C src minilucy.native
	cp src/minilucy.native .

src/avrlib.o: src/avrlib.c src/avrlib.h
	avr-gcc -g -fno-exceptions -Wall \
		      -O2 -Wnarrowing -Wl,-Os -fdata-sections \
          -ffunction-sections -Wl,-gc-sections \
          -mmcu=atmega328p -DF_CPU=16000000 \
	        -c $< -o $@

src/liquidCrystal.o: src/liquidCrystal.c src/liquidCrystal.h
	avr-gcc -g -fno-exceptions -Wall \
		      -O2 -Wnarrowing -Wl,-Os -fdata-sections \
          -ffunction-sections -Wl,-gc-sections \
          -mmcu=atmega328p -DF_CPU=16000000 \
	        -c $< -o $@

tests: minilucy.native
	cd tests && ./runtests.sh

samples: minilucy.native
	make -C samples

rapport.pdf: rapport.tex
	pdflatex rapport.tex

clean:
	rm -f *.native
	make -C src clean
	make -C samples clean

.PHONY: all tests samples clean
