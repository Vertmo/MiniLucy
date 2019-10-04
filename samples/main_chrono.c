#include <stdio.h>
#include "chrono.c"

int main() {
  chrono_mem mem;
  chrono_out out;

  chrono_reset(&mem);

  // Lancer le comptage
  chrono_step(1, 0, &mem, &out);
  printf("%dm%ds\n", out.disp_2, out.disp_1);

  // On court !
  int i;
  for(i = 0; i < 9300; i++) {
    chrono_step(0, 0, &mem, &out);
  }

  // LAP !
  chrono_step(1, 0, &mem, &out);
  printf("%dm%ds\n", out.disp_2, out.disp_1);

  // RESET !
  chrono_step(0, 1, &mem, &out);
  printf("%dm%ds\n", out.disp_2, out.disp_1);
  return 0;
}
