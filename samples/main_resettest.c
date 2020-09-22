#include <stdio.h>
#include "resettest.c"

int main() {
  test1_out out;
  test1_mem mem;

  test1_reset(&mem);

  int i;
  for(i = 0; i < 10; i++) {
    test1_step((i % 3 == 0), &mem, &out);
    printf("%d\n", out.y);
  }
  return 0;
}
