#include <stdio.h>
#include "fulladder.c"

int main() {
  full_add_h_out out;
  full_add_h_mem mem;

  full_add_h_reset(&mem);
  full_add_h_step(1, 0, 1, &mem, &out);
  printf("s=%d; co=%d", out.s, out.co);

  return 0;
}
