## GateGen 2

The library to generate Gate circuits (from gatesim library).
This version uses current generic-array-1.x library.

This library provides structures to create boolean formula from
boolean expressions and integer expressions. The module `gate` provides
basic types, traits to handle clauses and literals.
The `boolexpr` module provides structure to construct boolean
expressions. The `intexpr` and `dynintexpr` modules provide structure and traits to
construct integer expressions.

Same construction of expressions can be done in natural way by using operators or
methods. The object called `ExprCreator` holds all expressions. The main structures
that allow construct expressions are expression nodes: `BoolExprNode`, `IntExprNode`
and `DynIntExprNode`. BoolExprNode allow to construct boolean expressions.
`IntExprNode` and `DynIntExprNode` allows to construct integer expressions or multiple
bit expressions.

Typical usage of this library is: construction boolean expression and write it by using
method `to_circuit` or other similar method from an expression object to generate
Gate circuit.

This version offers new interface to operate on expressions.
This interface in `boolvar`, `intvar` and `dynintvar` modules. New interface offers
few simplifications that facility writing complex expressions.
New `boolvar` module provides simpler interface to construct boolean expressions.
New `intvar` module provides simpler interface to construct integer expressions.
New `dynintvar` module provides simpler interface to construct dynamic integer expressions.
The routine that creates new expression must be called inside `call16`, `call32` or `callsys`.
That routine can returns formula to generate. The `BoolVar` allows to operate on boolean
expressions, `IntVar` allows to operate on integer expressions and `DynIntVar` allows to
operate on dynamic integer expressions. These types can be used as references and
constants be converted into one of that type by using From trait.

This version contains `min` and `max` helpers, new an optimized tables and If-Then-Else and
and additional `subvalues` method to dynamic integers.

Sample example in new interface:

```rust
use gate_calc_log_bits::*;
use gategen2::boolvar::*;
use gategen2::dynintvar::*;
use gategen2::*;
use gatesim::*;

// program that generates circuit that check whether number 'a' (encoded in cirucit) is
// divisible by input number ('half_x'). Circuit is unsatisifiable if 'a' is prime.
fn main() {
    let a: u128 = 458581; // some number.
    // calculate bits for 'a' number.
    let bits = calc_log_bits_u128(a);
    // use half of bits to calculate bits of square root of number.
    let half_bits = (bits + 1) >> 1;
    // call a generating routine in callsys to.
    let circuit = callsys(|| {
        // x have half of bits of 'a' number.
        let half_x = UDynVarSys::var(half_bits);
        let a = UDynVarSys::from_n(a, bits);
        let x = half_x
            .clone()
            .concat(UDynVarSys::from_n(0u8, bits - half_bits));
        // calculate modulo: a modulo x.
        let (res_mod, cond) = a % &x;
        // formula: modulo must be 0 and x must not be 0 (from cond) and must x != 1.
        let formula = res_mod.equal(0u8) & cond & x.nequal(1u8);
        formula.to_translated_circuit(half_x.iter())
    });
    print!("{}", FmtLiner::new(&circuit, 4, 8));
}
```

Sample example in older interface:

```rust
use gate_calc_log_bits::*;
use gategen2::boolexpr::*;
use gategen2::dynintexpr::*;
use gategen2::*;
use gatesim::*;

// program that generates circuit that check whether number 'a' (encoded in cirucit) is
// divisible by input number ('half_x'). Circuit is unsatisifiable if 'a' is prime.
fn main() {
    let a: u128 = 557681; // some number.
    // calculate bits for 'a' number.
    let bits = calc_log_bits_u128(a);
    // use half of bits to calculate bits of square root of number.
    let half_bits = (bits + 1) >> 1;
    let creator = ExprCreatorSys::new();
    // x have half of bits of 'a' number.
    let half_x = UDynExprNode::variable(creator.clone(), half_bits);
    let a = UDynExprNode::try_constant_n(creator.clone(), bits, a).unwrap();
    let x = half_x
        .clone()
        .concat(UDynExprNode::try_constant_n(creator.clone(), bits - half_bits, 0u8).unwrap());
    // calculate modulo: a modulo x.
    let (res_mod, cond) = a % x.clone();
    // zero and one - constant values.
    let zero = UDynExprNode::try_constant_n(creator.clone(), bits, 0u8).unwrap();
    let one = UDynExprNode::try_constant_n(creator.clone(), bits, 1u8).unwrap();
    // formula: modulo must be 0 and x must not be 0 (from cond) and must x != 1.
    let formula: BoolExprNode<_> = res_mod.equal(zero) & cond & x.clone().nequal(one.clone());
    let circuit = formula.to_translated_circuit(half_x.iter());
    print!("{}", FmtLiner::new(&circuit, 4, 8));
}
```
