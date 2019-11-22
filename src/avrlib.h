#include <stdbool.h>
#include <util/delay.h>
#include <util/atomic.h>
#include <avr/io.h>
#include <avr/interrupt.h>

#ifndef __AVR_LIB__
#define __AVR_LIB__

/******************************************************************************/

#define PIN0 0
#define PIN1 1
#define PIN2 2
#define PIN3 3
#define PIN4 4
#define PIN5 5
#define PIN6 6
#define PIN7 7
#define PIN8 8
#define PIN9 9
#define PIN10 10
#define PIN11 11
#define PIN12 12
#define PIN13 13
#define PINA0 14
#define PINA1 15
#define PINA2 16
#define PINA3 17
#define PINA4 18
#define PINA5 19

#define INPUT 0
#define OUTPUT 1

#define LOW 0
#define HIGH 1

/******************************************************************************/

void avr_pin_mode(uint8_t pin, uint8_t mode);

void avr_digital_write(uint8_t pin, uint8_t level);
uint8_t avr_digital_read(uint8_t pin);

void avr_analog_write(uint8_t pin, int val);
uint16_t avr_analog_read(uint8_t ch);

void avr_delay(int ms);
int avr_millis();

/******************************************************************************/

#endif
