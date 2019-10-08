include Makefile.conf

all: minilucy.byte src/avrlib.o samples

minilucy.byte: $(addprefix src/,$(SRC))
	make -C src minilucy.byte
	cp src/minilucy.byte .

src/avrlib.o: src/avrlib.c
	avr-g++ -g -fno-exceptions -Wall -std=c++11 \
		      -O2 -Wnarrowing -Wl,-Os -fdata-sections \
          -ffunction-sections -Wl,-gc-sections \
          -mmcu=atmega328p -DF_CPU=16000000 \
	        -c $^ -o $@

samples: minilucy.byte
	make -C samples

rapport.pdf: rapport.tex
	pdflatex rapport.tex

clean:
	rm -f *.byte
	make -C src clean
	make -C samples clean
