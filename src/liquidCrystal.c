#include <stdlib.h>
#include <string.h>
#include "liquidCrystal.h"

/******************************************************************************/

lcd *create_lcd(uint8_t rs, uint8_t enable,
                uint8_t d0, uint8_t d1, uint8_t d2, uint8_t d3) {
  lcd *lcd = malloc(sizeof(lcd));
  lcd->rs = rs;
  lcd->enable = enable;
  lcd->ds[0] = d0; lcd->ds[1] = d1; lcd->ds[2] = d2; lcd->ds[3] = d3;
  lcd->displayFunction = LCD_4BITMODE | LCD_1LINE | LCD_5x8DOTS;
  lcd->displayMode = 0;
  lcd->displayControl = 0;
  lcd->numLines = 1;
  lcd_begin(lcd, 2, 16);
  return lcd;
}

void set_row_offsets(lcd *lcd, uint8_t r0, uint8_t r1, uint8_t r2, uint8_t r3) {
  lcd->rowOffsets[0] = r0;
  lcd->rowOffsets[1] = r1;
  lcd->rowOffsets[2] = r2;
  lcd->rowOffsets[3] = r3;
}

/******************************************************************************/
/* Low level primitives                                                       */

void pulse_enable(lcd *lcd) {
  avr_digital_write(lcd->enable, LOW);
  avr_delay(1);
  avr_digital_write(lcd->enable, HIGH);
  avr_delay(1);
  avr_digital_write(lcd->enable, LOW);
  avr_delay(1);
}

void write_4_bits(lcd *lcd, uint8_t value) {
  for(int i = 0; i < 4; i++) {
    avr_digital_write(lcd->ds[i], ((value >> i)&0x01));
  }
  pulse_enable(lcd);
}

void send(lcd *lcd, uint8_t value, uint8_t mode) {
  avr_digital_write(lcd->rs, mode);

  write_4_bits(lcd, (value >> 4));
  write_4_bits(lcd, value);
}

/******************************************************************************/
/* Mid level commands                                                         */

void command(lcd *lcd, uint8_t value) {
  send(lcd, value, LOW);
}

void write(lcd *lcd, char value) {
  send(lcd, value, HIGH);
}

/******************************************************************************/
/* High level user commands                                                   */

void lcd_begin(lcd *lcd, int c, int l) {
  if(l > 1) lcd->displayFunction |= LCD_2LINE;
  lcd->numLines = l;

  set_row_offsets(lcd, 0x00, 0x40, (0x00+c), (0x40+c));

  // Set output modes for the pins
  avr_pin_mode(lcd->rs, OUTPUT);
  avr_pin_mode(lcd->enable, OUTPUT);
  for(int i = 0; i < 4; i++) avr_pin_mode(lcd->ds[i], OUTPUT);

  // We wait for a bit
  avr_delay(50);

  avr_digital_write(lcd->rs, LOW);
  avr_digital_write(lcd->enable, LOW);

  // Set the display function
  write_4_bits(lcd, 0x03);
  avr_delay(5);
  write_4_bits(lcd, 0x03);
  avr_delay(5);
  write_4_bits(lcd, 0x03);
  avr_delay(1);
  write_4_bits(lcd, 0x02);
  command(lcd, (LCD_FUNCTIONSET | lcd->displayFunction));

  // Turn the display on
  lcd->displayControl = LCD_DISPLAYON | LCD_CURSOROFF | LCD_BLINKOFF;
  display(lcd);

  // Clear the display
  clear(lcd);

  // Set entry mode
  lcd->displayMode = LCD_ENTRYLEFT | LCD_ENTRYSHIFTDECR;
  command(lcd, LCD_ENTRYMODESET | lcd->displayMode);
}

void clear(lcd *lcd) {
  command(lcd, LCD_CLEARDISPLAY);
  avr_delay(2);
}

void home(lcd *lcd) {
  command(lcd, LCD_RETURNHOME);
  avr_delay(2);
}

void print(lcd *lcd, char *str) {
  int n = strlen(str);
  for(int i = 0; i < n; i++) {
    write(lcd, str[i]);
  }
}

void create_char(lcd *lcd, uint8_t loc, uint8_t content[8]) {
  loc &= 0x07;
  command(lcd, LCD_SETCGRAMADDR | (loc << 3));
  for(int i = 0; i<8; i++) write(lcd, content[i]);
}

void display(lcd *lcd) {
  lcd->displayControl |= LCD_DISPLAYON;
  command(lcd, LCD_DISPLAYCONTROL | lcd->displayControl);
}

void blink(lcd *lcd) {
  lcd->displayControl |= LCD_BLINKON;
  command(lcd, LCD_DISPLAYCONTROL | lcd->displayControl);
}
