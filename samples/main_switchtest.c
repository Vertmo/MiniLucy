#include <stdio.h>
#include "switchtest.c"

int main() {
  test5_out out;
  test5_mem mem;

  test5_reset(&mem);

  int i;
  for(i = 0; i < 10; i++) {
    test5_step(&mem, &out);
    printf("%d\n", out.z);
  }
  return 0;
}
