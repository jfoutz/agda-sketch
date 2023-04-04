https://plfa.github.io/Naturals/

plfa provides instructions for installing agda and the fabulous agda-stdlib.

The agda stdlib is a bit overwhelming.

Let's ruthelessly simplify the generality of equality

```
module natsketch where
open import Agda.Builtin.Nat
open import Agda.Builtin.Equality

```

https://github.com/agda/agda/blob/master/src/data/lib/prim/Agda/Builtin/Equality.agda

Builtin equality provides, ≡ both sides evaluate to the same thing.
2+2 ≡ 2*2
4 ≡ 4
refl, is identity
```
_ : zero ≡ zero
_ = refl

```


https://github.com/agda/agda-stdlib/blob/198f176fb0309b1f9591f9ff5946fc1dbf5e6de8/src/Relation/Binary/PropositionalEquality/Core.agda#L103

we can see how equality works above, we can crib some of that tooling for the simple proofs we're attempting with Nat.

we can always improve these definitions in another module, or adopt the generalized stdlib implementations.

```
infix  3 _qed
infixr 2 _<>_
infix  1 begin_

{-
this enables generalization across more types.

private
  variable
    A : Set

adding level above would include even more types.
-}
-- begin_ : ∀{x y : A} → x ≡ y → x ≡ y
begin_ : {x y : Nat} -> x ≡ y -> x ≡ y
begin_ x≡y = x≡y

-- _<>_ : ∀ (x {y} : A) → x ≡ y → x ≡ y
_<>_ : (x {y} : Nat) -> x ≡ y -> x ≡ y
_ <> x≡y = x≡y

-- _qed : ∀ (x : A) → x ≡ x
_qed : (x : Nat) -> x ≡ x
_qed _ = refl
```


```
_ : 2 + 3 ≡ 5
_ = begin
    2 + 3
  <>
    (suc(suc zero) + (suc (suc (suc zero))))
  qed
```
this is cute, but not super clear. it's relying on Nat magic to convert 2 to suc (suc zero)

so what does this machine actually do?

begin_ looks like good old identity

qed applies refl to the one and only argument

could be phrased as
```
_ : zero ≡ zero
_ = begin zero
    qed
```

begin isn't really needed, we can just pass the the argument to it

```
_ : zero ≡ zero
_ = zero qed
```
and really, the machine isn't needed, yet

```
_ : zero ≡ zero
_ = refl
```
so we've seen some nat magic already, 2 -> (suc (suc zero))
let's dodge builtin nat magic to get a better handle on equality.

```
data sN : Set where
 zz : sN
 ss : sN -> sN

_ : sN
_ = ss (ss zz)
```
and a few values

```
s0 : sN
s0 = zz
s1 : sN
s1 = ss zz
s2 : sN
s2 = ss s1

```
and maybe add
```
s+ : sN -> sN -> sN
s+ zz b = b
s+ (ss a) b =  s+ a (ss b)
```

now, can we show s+ s1 s1 ≡ s2?

well, we messed up our machine. it only works on Nat.
so let's build a new proof machine

we need something to kick it off, and we need to end with refl
```

sb_ : {x y : sN} -> x ≡ y -> x ≡ y
sb_ x≡y = x≡y

_sq : (x : sN) -> x ≡ x
_sq x≡y = refl

```
now we start to see the importance of the infix operations.
qed needs to bind tightest, and work backwards to begin.

when we've got a better understandign of ≡, we can build more substantial tooling,
or just rely on the stdlib.

```
infix  3 _sq
infixr 2 _<s>_
infix  1 sb_

_ : s0 ≡ s0
_ = refl

_ : s0 ≡ s0
_ = sb (s0 sq)
```

to make addition work, we need the <> operation to move things around

```
_<s>_ : (x {y} : sN) -> x ≡ y -> x ≡ y
_ <s> x≡y = x≡y
```

and the moment of truth.

```
_ : (s+ s0 s0) ≡ s0
_ = sb s0
    sq

_ : (s+ s1 s0) ≡ s1
_ = sb s1
    sq

_ : (s+ s1 s1) ≡ s2
_ = sb s2
    sq

_ : s2 ≡ (s+ s1 s1)
_ = sb s2
    sq
```

soo that is just providing a value for the equality.
can we show any sN + zero = sN?

```
t1_ : (x : sN) -> (s+ s0 x) ≡ x
t1_ x = sb (s+ s0 x)
        <s> x
        sq

t2_ : (x : sN) -> (s+ x s0) ≡ x
t2 zz = refl
t2 ss zz = {!!}
t2 ss (ss x) = {!!}
```
no. no we can't. and the reason is <s> is broken and wrong.
it's not obvious how to unpack the agda source to see what's really going on.

Lucky for me Jesper Cockx has a tutorial here - https://github.com/jespercockx/agda-lecture-notes/blob/master/agda.pdf
page 24 - refl!

also the cool _<_>_ which uses trasitive equality.

... so let's go understand that.
