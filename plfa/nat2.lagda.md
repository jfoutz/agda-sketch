ok, soooo was missing some keys to proofs.
so, try again.

this is glossing over levels. I don't have a deep understanding of them yet. So i don't think I can say things like list of list of nat yet.

i'm leaving things out so i get stuck. and then figure out why i'm stuck.

anyway.

```
module nat2 where

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

{-# BUILTIN NATURAL Nat #-}

_+_ : Nat -> Nat -> Nat
zero    + y = y
(suc x) + y = suc (x + y)

```
Exercise 1.1. Define the function halve : Nat → Nat that computes the result of dividing the given number by 2 (rounded down). Test your definition by evaluating it for several concrete inputs.
```

halve : Nat -> Nat
halve zero = zero
halve (suc zero) = zero -- half 1 is zero
halve (suc (suc x)) = suc (halve x)

th1 : Nat
th1 = halve 5
th2 : Nat
th2 = halve 10

```
Exercise 1.2. Define the function _*_ : Nat → Nat → Nat for multiplication of two natural numbers.

```

_*_ : Nat -> Nat -> Nat
zero  * y = zero
suc x * y =  y + (x * y)
t*1 : Nat
t*1 = 2 * 3
t*2 : Nat
t*2 = 5 * 5

```

Exercise 1.3. Define the type Bool with constructors true and false,
and define the functions for negation not : Bool → Bool, conjunction
_&&_ : Bool → Bool → Bool, and disjunction _||_ : Bool → Bool → Bool

```
data Bool : Set where
  true  : Bool
  false : Bool

not : Bool -> Bool
not true  = false
not false = true

_&&_ : Bool -> Bool -> Bool
true && true = true
_    && _ = false

_||_ : Bool -> Bool -> Bool
false || false = false
_     || _     = true
```

...

```
id : {A : Set} -> A -> A
id x = x
```
skipping if_then_else_ for now.
this is a little side effecty- this works great in haskell, because of lazy evaluation
but here, if either branch is expensive, you always pay the price (as far as i can tell)
it might be handy later, but, i, i just don't want to.

this does highlight that mixfix is prety cool.

```

data List (A : Set) : Set where
  [] : List A
  _::_ : A -> List A -> List A

infixr 5 _::_

data _×_ (A B : Set) : Set where
  _,_ : A -> B -> A × B

infix 4 _,_

```
odds are good i'll need fst and snd, sooo.

```
fst : {A B : Set} -> A × B -> A
fst (x , _) = x

snd : {A B : Set} -> A × B -> B
snd (_ , y) = y
```

Exercise 1.4. Implement the following Agda functions:

Nat
• length:{A:Set}→ListA→
• _++_:{A:Set}→ListA→
List A → List A
• map:{AB:Set}→(A→B)→
List A → List B

```

length : {A : Set} -> List A -> Nat
length []        = zero
length (x :: xs) = suc (length xs)

_++_ : {A : Set} -> List A -> List A -> List A
[] ++ y        = y
(x :: xs) ++ y = x :: (xs ++ y)

map : {A B : Set} -> (A -> B) -> List A -> List B
map f []        = []
map f (x :: xs) = (f x) :: (map f xs)
```

Exercise 1.5. Implement the type Maybe A with two constructors just : A → Maybe A and nothing : Maybe A. Next, implement the function lookup : {A:Set}→List A→Nat→Maybe A that returns the element at the given position in the list.

```
data Maybe (A : Set) : Set where
  nothing : Maybe A
  just    : A -> Maybe A


lookup : {A : Set} -> List A -> Nat -> Maybe A
lookup [] _              = nothing
lookup (x :: xs) zero    = just x
lookup (x :: xs) (suc i) = lookup xs i
```
Exercise 1.6. Is it possible to implement a function of type {A : Set} →
List A → Nat → A in Agda? If yes, do so. If no, explain why not.

so, i can't think of a way to get an A for any A.
for example
data No where
-- yeah no impl

So given a List No, what, uh, could you do?
