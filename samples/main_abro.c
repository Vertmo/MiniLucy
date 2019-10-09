#include <stdio.h>
#include "abro.c"

int main() {
  abro_mem mem;
  abro_out out;

  abro_reset(&mem);

  abro_step(0, 0, 0, &mem, &out);
  printf("%d\n", out.o);
  abro_step(0, 1, 0, &mem, &out);
  abro_step(0, 0, 0, &mem, &out);
  printf("%d\n", out.o);
  abro_step(1, 0, 0, &mem, &out);
  printf("%d\n", out.o);
  abro_step(1, 0, 0, &mem, &out);
  printf("%d\n", out.o);
  abro_step(0, 0, 1, &mem, &out);
  printf("%d\n", out.o);
  abro_step(1, 1, 0, &mem, &out);
  printf("%d\n", out.o);
  return 0;
}
