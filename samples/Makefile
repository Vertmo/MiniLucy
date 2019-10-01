MINILUCY := ../minilucy.byte

TARGETS := \
	fulladder.elf bananas.elf heat.elf abro.elf \
	clocktest.elf automatatest.elf \
	typetest.c causalitytest.c translationtest.c automatatest.c

all: $(TARGETS)

%.elf: main_%.c %.c
	gcc -o $@ $<

%.c: %.lus
	$(MINILUCY) -asserts -o $@ $^

clean:
	rm -f $(TARGETS)
