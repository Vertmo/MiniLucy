#include <stdio.h>
#include "typetest.c"

int main() {
  printf("Test test_fby\n====================\n");
  test_fby_mem mem1;
  test_fby_out out1;
  test_fby_reset(&mem1);

  for(int i = 0; i < 10; i++) {
    test_fby_step(&mem1, &out1);
    printf("%d\n", out1.z);
  }
  return 0;
}
