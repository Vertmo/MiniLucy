# MiniLucy compiler

Realized for the course Synchronous Systems at MPRI (see https://www.di.ens.fr/~pouzet/cours/mpri/projet/minilucy.pdf)

## Notes

### Clock-checking of function application

If we have the declaration 

`node f(a1, ..., an) -> (b1, ..., bn)`

and the application

`f(e1, ..., en) every ev`

where `ai` is clocked on `cai`, `bi` on `cbi`, `ei` on `cei` and `ev` on `cev`

then the node will be executed on `cev`, and the unification is made by composing formal parameters with `cev`: `cei = cai o cev` for input, `cbi o cev` for output.

What's more difficult to process is the substitution operation : if an indentifier `ai` appears in the type of a formal parameter, the corresponding actual parameter `ei` (which must be an indentifier) must be swapped in it's place (similarly in the outputs)

Also prevents some stuff such as:
```
node test_app2(b1 : bool; b2 : bool when b1; c1 : bool when b1) returns (z : int when c1);
let
  z = test_when(b1, c1) every b2;
tel;
```
where b1 would need to be "on b1" for it to work

### Automata

Clocks are used to discriminate between expressions in different states.
This means equation must be defined in every state for a given value (possibility of local binding in automaton).

State clock are defined from merged `until` equations

#### Resets

A bit more difficult. An application must be on a proper clock in order to execute only at the right times

Solutions:

Use a reset clock on the same clock as the branches clock. This clock will be defined during any step the automaton is active in. This means that the functions will be called too much (not a problem since it is reset + no side effect)

Example:
```
node auto_simpl() returns (x : int);
let
  automaton
  | INC ->
    x = 0 fby x + 1;
    until x = 5 then DEC;
  | DEC ->
    x = 0 fby x - 2;
    until x = -10 then INC;
  end;
tel;
```

becomes 

```
node auto_simpl() returns (x:int);
var _auto_state1:_ty_auto_state1; _auto_state1INC_reset:bool; _auto_state1DEC_reset:bool;
let
  x = merge _auto_state1 
      (DEC -> (if [(false fby _auto_state1DEC_reset) when DEC(_auto_state1); 0 when DEC(_auto_state1); (0 fby (- [x; 2]) when DEC(_auto_state1))])) 
      (INC -> (if [(false fby _auto_state1INC_reset) when INC(_auto_state1); 0 when INC(_auto_state1); (0 fby (+ [x; 1]) when INC(_auto_state1))]));

  _auto_state1 = (INC fby merge _auto_state1 (DEC -> (if [(= [x; (- [10])]); INC; DEC]) when DEC(_auto_state1)) (INC -> (if [(= [x; 5]); DEC; INC]) when INC(_auto_state1)));
  _auto_state1INC_reset = merge _auto_state1 (DEC -> true when DEC(_auto_state1)) (INC -> false when INC(_auto_state1));
  _auto_state1DEC_reset = merge _auto_state1 (DEC -> false when DEC(_auto_state1)) (INC -> true when INC(_auto_state1));
tel
```

Test for when / merge in expressions (+ every for functions could cause an issue, replace it totally by the reset clock ?)
