#include <stdio.h>
#include "uselib.c"

int main() {
  main_mem mem;
  main_out out;

  main_reset(&mem);
  for(int i = 0; i < 10; i++) {
    main_step(&mem, &out);
    printf("%d\n", out.f);
  }

  return 0;
}
