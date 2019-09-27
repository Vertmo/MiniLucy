#include <stdio.h>
#include "bananas.c"

int main() {
  count_bananas_out out;
  count_bananas_mem mem;

  count_bananas_reset(&mem);

  int i;
  for(i = 0; i < 10; i++) {
    count_bananas_step(i%2, &mem, &out);
  }
  printf("%d\n", out.n);
  return 0;
}
