# stuff!

```
module plfa-ch1 where

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

{-# BUILTIN NATURAL Nat #-}

data _≡_ {A : Set} : A -> A -> Set where
  refl : { x : A } -> x ≡ x

infix 4 _≡_

_+_ : Nat -> Nat -> Nat
zero + n = n
(suc m) + n = suc (m + n)

one-plus-one : 1 + 1 ≡ 2
one-plus-one = refl

trans : {A : Set} { x y z : A } -> x ≡ y -> y ≡ z -> x ≡ z
trans refl refl = refl

begin_ : { A : Set } -> {x y : A} -> x ≡ y -> x ≡ y
begin p = p

_=<_>_ : { A : Set } -> (x : A) -> { y z : A }
         -> x ≡ y
         -> y ≡ z
         -> x ≡ z
x =< y > z = trans y z

_=<>_ : { A : Set } -> (x : A) -> { y : A } -> x ≡ y -> x ≡ y
x =<> y = x =< refl > y


_end : { A : Set } -> ( x : A ) -> x ≡ x
x end = refl

infix 1 begin_
infix 3 _end
infixr 2 _=<_>_
infixr 2 _=<>_


```
so cheated a little bit to get the proof machine, 1+1 to test refl.
sooo, we have + already
probably going to need ⊤ and ⊥ soon.
```

_*_ : Nat -> Nat -> Nat
zero    * n = zero
(suc m) * n = n + (m * n)

_ =
  begin
    3 * 4
  =<>
    4 + (2 * 4)
  =<>
    4 + (4 + ( 1 * 4 ))
  =<>
    4 + (4 + (4 + ( zero * 4 )))
  =<>
    4 + (4 + 4)
  =<>
    4 + 8
  =<>
    12
  end

_^_ : Nat -> Nat -> Nat
m ^ zero = 1
m ^ (suc n) = m * (m ^ n)

_ =
  begin
    2 ^ 3
  =<>
    2 * (2 ^ 2)
  =<>
    2 * (2 * (2 ^ 1))
  =<>
    2 * (2 * (2 * (2 ^ 0)))
  =<>
    2 * (2 * (2 * 1))
  =<>
    2 * (2 * 2)
  =<>
    2 * 4
  =<>
    8
  end
