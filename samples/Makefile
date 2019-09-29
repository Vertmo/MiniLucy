MINILUCY := ../minilucy.byte

all: fulladder.elf bananas.elf heat.elf clocktest.elf

%.elf: main_%.c %.c
	gcc -o $@ $<

%.c: %.lus
	$(MINILUCY) -asserts -o $@ $^

clean:
	rm -f *.elf *.o
