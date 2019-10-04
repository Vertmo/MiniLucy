MINILUCY := ../minilucy.byte

TARGETS := \
	fulladder.elf bananas.elf heat.elf abro.elf \
	clocktest.elf automatatest.elf chrono.elf \
	typetest.c causalitytest.c translationtest.c

all: $(TARGETS)

%.elf: main_%.c %.c
	g++ -o $@ $<

%.c: %.lus
	$(MINILUCY) -asserts -o $@ $^

clean:
	rm -f $(TARGETS)
