#include <stdio.h>
#include <unistd.h>
#include "heat.c"

int main() {
  main_out out;
  main_mem mem;

  main_reset(&mem);

  // Let's heat up to a cozy 27C
  float target = 27;
  while(1) {
    main_step(target, &mem, &out);
    printf("Temp: %f\n", out.temp);
    usleep(100000);
  }
  return 0;
}
