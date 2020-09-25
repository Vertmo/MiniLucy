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
    printf("x : %d, y : %d\n", out2.x, out2.y);
  }

  printf("Test auto_app\n====================\n");
  auto_app_mem mem3;
  auto_app_out out3;
  auto_app_reset(&mem3);

  for(int i = 0; i < 30; i++) {
    auto_app_step(&mem3, &out3);
    printf("x : %d\n", out3.x);
  }


  printf("Test auto_last\n====================\n");
  auto_last_mem mem4;
  auto_last_out out4;
  auto_last_reset(&mem4);

  for(int i = 0; i < 30; i++) {
    auto_last_step(&mem4, &out4);
    printf("y : %d\n", out4.y);
  }
  return 0;
}
