# First step: Affine, linear, and unrestricted types

We are now desigining a new programming language with a type system that includes affine, linear, and unrestricted types.

## Files

- Types: rocq/theories/TypeSystem/Types.v,
- Syntax: rocq/theories/TypeSystem/Syntax.v

## Goal

1. Define the operational semantics of the language in rocq/theories/TypeSystem/OperationalSemantics.v.
2. Implment the typing rules of regarding the usage of variables in rocq/theories/TypeSystem/TypingRules.v.
3. Implement a type checker that can check the usage of affine, linear, and unrestricted types in a simple programming language in rocq/theories/TypeSystem/TypeChecker.v. Extracted this file to OCaml in fixtures/TypeChecker.ml.
4. Implement theorems in rocq/theories/TypeSystem/CheckerSoundness.v that the type checker is sound with respect to the operational semantics regarding the usage of variables.

## Affine types

Affine types allow at most one use of a variable. After the variable is used, it cannot be used again.

### Invalid use of affine variables

```pseudocode
let x: affine int = 10;
let y: affine int = x; // OK. y == 10, x is moved to y
let z: affine int = x; // error: use of affine variable `x` after move
```

### Valid use of affine variables

```pseudocode
let x: affine int = 10;
let y: affine int = x; // OK. y == 10
```

## Linear types

### Invalid use of linear variables

```pseudocode
let x: linear int = 10;
let y: linear int = x; // error: y must be used once
```

```pseudocode
let x: linear int = 10;
let y: linear int = replace(x, 20); // OK. x == 20, y == 10
drop(y);
// Error: x is not used after the replace
```

```pseudocode
let x: linear int = 10;
let y: affine int = x; // error: x may not be used after move
```

```pseudocode
let x: linear int = 10;
let y: unrestricted int = x; // error: x may not be used after move
```

```pseudocode
let x: affine int = 10;
let y: unrestricted int = x; // error: x may used more than once
```

### Valid use of linear variables

```pseudocode
let x: linear int = 10;
let y: linear int = x;
drop(y); // OK. y is dropped, so the error is resolved
```

```pseudocode
let x: linear int = 10;
let y: linear int = replace(x, 20); // OK. replace x with 20 and return 10, x == 20, y == 10
drop(x); // OK. x is dropped
drop(y); // OK. y is dropped
```

```pseudocode
let x: affine int = 10;
let y: linear int = x; // OK.
```

## Unrestricted types

```pseudocode
let x: unrestricted int = 10;
let y: unrestricted int = x; // OK. y == 10, x is still valid
let z: unrestricted int = x; // OK. z == 10, x is still valid
```

## Subtyping Rule

```
unrestricted  <:  affine  <:  linear
```

## Operational semantics

- replace(x, y)
  - x means the place of x (place x)
  - replaces the value of x with y and returns the old value of x. the returned type is the same as x's type.
  - x is not consumed by replace
  - y is consumed if it is affine or linear
- drop(x)
  - drops the variable x, which means that x is consumed and cannot be used again if x is affine or linear.
  - if x is unrestricted, then drop(x) does nothing and x can still be used again.
- let x: T = e1 in e2
  - evaluates e1 to a value v, binds x to v, and then evaluates e2.
  - if e1 is a linear or affine variable, then e1 is consumed and cannot be used again in e2.
  - ty_core(x) must be equal to ty_core(e1)
  - ty_usage(e1) <: ty_usage(x)
  - if x is linear, then x must be used exactly once in e2.
  - if x is affine, then x can be used at most once in e2.
- function application
  - if arguments are linear or affine variables, then they are consumed and cannot be used again after the function call.
  - if a function returns a linear value, then the caller must use the returned value exactly once.
  - if a function returns an affine value, then the caller can use the returned value at most once.

## Out of scope

- mutability checking
- ownership and borrowing
- ELetInfer
- TRef, TFn
