#include "avrlib.h"

/******************************************************************************/

volatile uint8_t *get_port_addr(uint8_t pin) {
  if (pin < 8) return &PORTD;
  if (pin < 14) return &PORTB;
  if (pin < 20) return &PORTC;
  return 0;
}

volatile uint8_t *get_pin_addr(uint8_t pin) {
  if (pin < 8) return &PIND;
  if (pin < 14) return &PINB;
  if (pin < 20) return &PINC;
  return 0;
}

volatile uint8_t *get_ddr_addr(uint8_t pin) {
  if (pin < 8) return &DDRD;
  if (pin < 14) return &DDRB;
  if (pin < 20) return &DDRC;
  return 0;
}

uint8_t get_bit(uint8_t pin) {
  if (pin < 14) return pin%8;
  return (pin + 2)%8;
}

/******************************************************************************/

#define NOT_ON_TIMER 0
#define TIMER0A 1
#define TIMER0B 2
#define TIMER1A 3
#define TIMER1B 4
#define TIMER1C 5
#define TIMER2  6
#define TIMER2A 7
#define TIMER2B 8

volatile uint8_t get_timer_of_pin(uint8_t pin) {
  if (pin == 3) return TIMER2B;
  if (pin == 5) return TIMER0B;
  if (pin == 6) return TIMER0A;
  if (pin == 9) return TIMER1A;
  if (pin == 10) return TIMER1B;
  if (pin == 11) return TIMER2A;
  return NOT_ON_TIMER;
}

/******************************************************************************/

void avr_set_bit(volatile uint8_t *reg, uint8_t bit) {
  *reg |= ((uint8_t) 1 << bit);
}

void avr_clear_bit(volatile uint8_t *reg, uint8_t bit) {
  *reg &= ~((uint8_t) 1 << bit);
}

bool avr_read_bit(volatile uint8_t *reg, uint8_t bit) {
  return *reg & ((uint8_t) 1 << bit);
}

/******************************************************************************/

void avr_pin_mode(uint8_t pin, uint8_t mode) {
  if(mode) avr_set_bit(get_ddr_addr(pin), get_bit(pin));
  else avr_clear_bit(get_ddr_addr(pin), get_bit(pin));
}

void avr_digital_write(uint8_t pin, uint8_t level) {
  if(level) avr_set_bit(get_port_addr(pin), get_bit(pin));
  else avr_clear_bit(get_port_addr(pin), get_bit(pin));
}

uint8_t avr_digital_read(uint8_t pin) {
  return avr_read_bit(get_pin_addr(pin), get_bit(pin));
}

/******************************************************************************/

#ifndef sbi
#define sbi(sfr, bit) (_SFR_BYTE(sfr) |= _BV(bit))
#endif

#ifndef cbi
#define cbi(sfr, bit) (_SFR_BYTE(sfr) &= ~_BV(bit))
#endif

void avr_analog_write(uint8_t pin, int val) {
  int timer = get_timer_of_pin(pin);

  switch(timer) {
  case TIMER0A:
    OCR0A = val;
    sbi(TCCR0A, COM0A1);
    TCCR0A |= (1 << WGM01) | (1 << WGM00);
    TCCR0B |= (1 << CS01);
    break;

  case TIMER0B:
    OCR0B = val;
    sbi(TCCR0A, COM0B1);
    TCCR0A |= (1 << WGM01) | (1 << WGM00);
    TCCR0B |= (1 << CS01);
    break;

  case TIMER1A:
    OCR1A = val;
    sbi(TCCR1A, COM1A1);
    TCCR1A |= (1 << WGM11) | (1 << WGM10);
    TCCR1B |= (1 << CS11);
    break;

  case TIMER1B:
    OCR1B = val;
    sbi(TCCR1A, COM1B1);
    TCCR1A |= (1 << WGM11) | (1 << WGM10);
    TCCR1B |= (1 << CS11);
    break;

  case TIMER2A:
    OCR2A = val;
    sbi(TCCR2A, COM2A1);
    TCCR2A |= (1 << WGM21) | (1 << WGM20);
    TCCR2B |= (1 << CS21);
    break;

  case TIMER2B:
    OCR2B = val;
    sbi(TCCR2A, COM2B1);
    TCCR2A |= (1 << WGM21) | (1 << WGM20);
    TCCR2B |= (1 << CS21);
    break;
  }

}

/******************************************************************************/

int is_inited = 0;

uint16_t avr_analog_read(uint8_t ch) {
  // We init the channel
  if(!is_inited) {
    ADMUX = (1<<REFS0);
    ADCSRA = (1<<ADEN)|(1<<ADPS2)|(1<<ADPS1)|(1<<ADPS0);

    is_inited = 1;
  }

  ch += 2;
  ch &= 0b00000111;  // AND operation with 7
  ADMUX = (ADMUX & 0xF8)|ch; // clears the bottom 3 bits before ORing
  // start single convertion
  // write ’1′ to ADSC
  ADCSRA |= (1<<ADSC);
  // wait for conversion to complete
  // ADSC becomes ’0′ again
  // till then, run loop continuously
  while(ADCSRA & (1<<ADSC));
  return (ADC);
}

/******************************************************************************/

void avr_delay(int ms) {
  while(ms--) {
    _delay_ms(1);
  }
}

/******************************************************************************/

/* millis function from https://github.com/monoclecat/avr-millis-function */

volatile int timer1_millis;

ISR(TIMER1_COMPA_vect)
{
  timer1_millis++;
}

int avr_millis() {
  int millis_return;

  // Ensure this cannot be disrupted
  ATOMIC_BLOCK(ATOMIC_FORCEON) {
    millis_return = timer1_millis;
  }
  return millis_return;

}

/******************************************************************************/
