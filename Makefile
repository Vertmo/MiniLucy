include Makefile.conf

all: minilucy.byte src/avrlib.o src/liquidCrystal.o samples

src/config.ml:
	make -C src config.ml

minilucy.byte: $(addprefix src/,$(SRC))
	make -C src minilucy.byte
	cp src/minilucy.byte .

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

samples: minilucy.byte
	make -C samples

rapport.pdf: rapport.tex
	pdflatex rapport.tex

clean:
	rm -f *.byte
	make -C src clean
	make -C samples clean
