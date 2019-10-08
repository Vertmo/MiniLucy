MINILUCY := ../minilucy.byte

TARGETS := \
	fulladder.elf bananas.elf heat.elf abro.elf \
	clocktest.elf typetest.elf \
	causalitytest.c translationtest.c sugartest.c uselib.elf \
  automatatest.elf chrono.elf \
	iotest.hex

all: $(TARGETS)

%.elf: main_%.c %.c
	g++ -o $@ $<

uselib.c : lib.lus uselib.lus
	$(MINILUCY) -asserts -o $@ $^

%.c: %.lus
	$(MINILUCY) -asserts -o $@ $^

%.hex: %.lus
	$(MINILUCY) -asserts -avr -o $@ $^

clean:
	rm -f $(TARGETS)
	rm -f *.elf *.o *.avr *.hex
