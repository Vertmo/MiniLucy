# MiniLucy compiler

Realized for the course Synchronous Systems at MPRI (see https://www.di.ens.fr/~pouzet/cours/mpri/projet/minilucy.pdf)

## Usage

* `make` to compile the project
* `make samples` to compile the test samples
* `./minilucy.byte` to use the compiler (`-help'` to see options)

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

Use a reset clock on the same clock as the state clock. This clock will be defined during any step the automaton is active in. This is not a problem as we add whens later on to subsample (in order to not call the functions too much)

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

Limitations:
* No when / merge (difficult to reset)
* No tuple assignment (difficult to form merge expressions) so only unary function applications
* No "every" : use generated reset clocks
Is this really an issue ? We can ask the user to chose between clocks and automata since the two features are two ways to express the same thing

### Interpreter

Using (unbounded) streams for the sake of simplicity. Will be (hopefully) used to check how the automaton semantics and kernel (translated) semantics coincide.

While using it, I found a big problem with clocks: suppose the equation

```
  x = merge b (True -> 0 fby (x when True(b))) (False -> 1 fby (x when False(b)))
```

Now, if the clocks are indeed influenced by the `fby`, and the `b` behind the `fby` refer to the previous value of `b`, then we have a problem, because the return value of this expression could be `Nil`. If the clocks are not influenced by `fby`, then we are prevented from doing something like:
```
  b = false fby (merge b (True -> false) (False -> true))
```
which would be a causality error. And I need this to compile automata !
