#include <stdio.h>
#include "automatatest.c"

int main() {
  printf("Test auto_simpl\n====================\n");
  auto_simpl_mem mem1;
  auto_simpl_out out1;
  auto_simpl_reset(&mem1);

  for(int i = 0; i < 30; i++) {
    auto_simpl_step(&mem1, &out1);
    printf("x : %d\n", out1.x);
  }

  printf("Test auto_mult\n====================\n");
  auto_mult_mem mem2;
  auto_mult_out out2;
  auto_mult_reset(&mem2);

  for(int i = 0; i < 30; i++) {
    auto_mult_step(&mem2, &out2);
    printf("x : %d\n", out2.x);
  }
  return 0;
}
