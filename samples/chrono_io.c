#include "liquidCrystal.h"

#define CLOCK_PERIOD 10

lcd *disp;

void io_init() {
  avr_pin_mode(PIN6, INPUT);
  avr_pin_mode(PIN7, INPUT);

  disp = create_lcd(12, 11, 5, 4, 3, 2);
}

int io_read_StSt() {
  return avr_digital_read(PIN6);
}

int io_read_Rst() {
  return avr_digital_read(PIN7);
}

int disp_s = 0;

void io_write_disp_1(int disp_1) {
  disp_s = disp_1;
}

int counter = 0;

void io_write_disp_2(int disp_2) {
  if(counter >= 50) {
    char buf[6];
    sprintf(buf, "%02d:%02d", disp_2, disp_s);
    clear(disp);
    print(disp, buf);
    counter = 0;
  }
  counter = (counter + 1);
}
