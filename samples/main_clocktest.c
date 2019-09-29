#include <stdio.h>
#include "clocktest.c"

int main() {
  test_merge_nary_mem mem;
  test_merge_nary_out out;

  test_merge_nary_reset(&mem);

  test_merge_nary_step(_clock_c3_D, &mem, &out);
  printf("D(a): %d\n", out.x);
  test_merge_nary_step(_clock_c3_E, &mem, &out);
  printf("E(a): %d\n", out.x);
  test_merge_nary_step(_clock_c3_F, &mem, &out);
  printf("F(a): %d\n", out.x);
  return 0;
}
