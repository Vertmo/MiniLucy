#include <stdio.h>
#include "fulladder.c"

int main() {
  full_add_h_out out;
  full_add_h_mem mem;

  full_add_h_reset(&mem);
  full_add_h_step(1, 0, 0, &mem, &out);
  printf("1,0,0 -> s=%d; co=%d\n", out.s, out.co);

  full_add_h_step(0, 1, 1, &mem, &out);
  printf("0,1,1 -> s=%d; co=%d\n", out.s, out.co);

  full_add_h_step(1, 1, 1, &mem, &out);
  printf("1,1,1 -> s=%d; co=%d\n", out.s, out.co);

  return 0;
}
