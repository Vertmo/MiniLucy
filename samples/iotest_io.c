#include "avrlib.h"

void io_init() {
  avr_pin_mode(PIN4, INPUT);
  avr_pin_mode(PIN5, INPUT);
  avr_pin_mode(PIN7, OUTPUT);

  avr_pin_mode(PINA1, INPUT);
  avr_pin_mode(PIN3, OUTPUT);
}

int io_read_b1() {
  return avr_digital_read(PIN4);
}

int io_read_b2() {
  return avr_digital_read(PIN5);
}

int io_read_x() {
  return avr_analog_read(PINA1);
}

void io_write_b(int b) {
  avr_digital_write(PIN7, b);
}

void io_write_y(int y) {
  avr_analog_write(PIN3, y);
}
