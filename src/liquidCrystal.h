#include "avrlib.h"

#ifndef __LIQUID_CRYSTAL__
#define __LIQUID_CRYSTAL__

typedef struct {
  uint8_t rs;
  uint8_t enable;
  uint8_t ds[4];
  uint8_t displayFunction;
  uint8_t displayMode;
  uint8_t displayControl;
  uint8_t numLines;
  uint8_t rowOffsets[4];
} lcd;

/******************************************************************************/

#define LCD_CLEARDISPLAY 0x01
#define LCD_RETURNHOME 0x02
#define LCD_ENTRYMODESET 0x04
#define LCD_DISPLAYCONTROL 0x08
#define LCD_CURSORSHIFT 0x10
#define LCD_FUNCTIONSET 0x20
#define LCD_SETCGRAMADDR 0x40
#define LCD_SETDDRAMADDR 0x80

#define LCD_DISPLAYON 0x04
#define LCD_DISPLAYOFF 0x00
#define LCD_CURSORON 0x02
#define LCD_CURSOROFF 0x00
#define LCD_BLINKON 0x01
#define LCD_BLINKOFF 0x00

#define LCD_ENTRYLEFT 0x02
#define LCD_ENTRYRIGHT 0x00
#define LCD_ENTRYSHIFTINCR 0x01
#define LCD_ENTRYSHIFTDECR 0x00

#define LCD_DISPLAYMOVE 0x08
#define LCD_CURSORMOVE 0x00
#define LCD_MOVELEFT 0x00
#define LCD_MOVERIGHT 0x04

#define LCD_8BITMODE 0x10
#define LCD_4BITMODE 0x00
#define LCD_2LINE 0x08
#define LCD_1LINE 0x00
#define LCD_5x10DOTS 0x04
#define LCD_5x8DOTS 0x00

/******************************************************************************/

lcd *create_lcd(uint8_t rs, uint8_t enable,
                uint8_t d0, uint8_t d1, uint8_t d2, uint8_t d3);
void lcd_begin(lcd *lcd, int columns, int rows);

void clear(lcd *lcd);
void home(lcd *lcd);
void set_cursor(lcd *lcd, int c, int r);

void write(lcd *lcd, char c);
void print(lcd *lcd, char *str);
void create_char(lcd *lcd, uint8_t loc, uint8_t content[8]);

void display(lcd *lcd);
void no_display(lcd *lcd);
void blink(lcd *lcd);
void no_blink(lcd *lcd);
void cursor(lcd *lcd);
void no_cursor(lcd *lcd);
void scroll_left(lcd *lcd);
void scroll_right(lcd *lcd);
void left_to_right(lcd *lcd);
void right_to_left(lcd *lcd);
void autoscroll(lcd *lcd);
void no_autoscroll(lcd *lcd);

/******************************************************************************/

#endif
