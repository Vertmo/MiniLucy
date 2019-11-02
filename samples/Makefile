MINILUCY := ../minilucy.byte

TARGETS := \
	fulladder.elf bananas.elf heat.elf abro.elf \
	clocktest.elf typetest.elf automatatest.elf chrono.elf \
	causalitytest.c translationtest.c sugartest.c uselib.elf

all: $(TARGETS)

%.elf: main_%.c %.c
	g++ -o $@ $<

uselib.c : lib.lus uselib.lus
	$(MINILUCY) -asserts -o $@ $^

%.c: %.lus
	$(MINILUCY) -asserts -o $@ $^

clean:
	rm -f $(TARGETS)
