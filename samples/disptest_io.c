#include <stdio.h>
#include "liquidCrystal.h"

#define CLOCK_PERIOD 1000

lcd *disp;

void io_init() {
  // Initialise the screen
  disp = create_lcd(12, 11, 5, 4, 3, 2);

  uint8_t ch[8] = {0,17,0,0,17,14,0};
  create_char(disp, 0, ch);

  lcd_begin(disp, 16, 2);
}

void io_write_x(int x) {
  clear(disp);
  char buf[15];
  sprintf(buf, "%d", x);
  print(disp, buf);
}
