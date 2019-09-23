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
