# Document Title
what the heck is a boolean? it's like a switch? off or on?
present or absent?

those are really different. a switch implies a fixed thing. one and only one.

```

module fun where

data Bool : Set where
  true : Bool
  false : Bool

```
as far as i can tell, there are exactly four functions.
A   0 1
-----------
0 | 0 0
1 | 0 1
2 | 1 0
3 | 1 1

```

zerob : Bool -> Bool
zerob _ = false

val : Bool -> Bool
val x = x

not : Bool -> Bool
not false = true
not true = false

one : Bool -> Bool
one _ = true

build : Bool -> Bool -> (Bool -> Bool)
build f t = \ where
              false -> f
              true  -> t

```
so that's like, fine.

f0 and f3 are forgetful. we can't figure out what a was originally

to identify what function it is, we have to check both cases of a.

```
_∘_ : {A B C : Set} -> (B -> C) -> (A -> B) -> (A -> C)
f ∘ g = \ x -> f (g x)
```
any arbitrary composition of the 4 possible function reduces to one of the four possible functions. That there, is a hell of a propositon.

let's build the proof machine.

```

data _≡_ {A : Set} : A -> A -> Set where
  refl : {x : A} -> x ≡ x

sym : {A : Set} {x y : A} -> x ≡ y -> y ≡ x
sym refl = refl

trans : {A : Set} { x y z : A } -> x ≡ y -> y ≡ z -> x ≡ z
trans refl refl = refl

cong : {A B : Set} { x y : A} -> (f : A -> B) -> x ≡ y -> f x ≡ f y
cong f refl = refl

begin_ : { A : Set } -> {x y : A} -> x ≡ y -> x ≡ y
begin p = p

_end : {A : Set} -> (x : A) -> x ≡ x
x end = refl

_=⟨_⟩_ : { A : Set } -> (x : A) -> {y z : A}
         -> x ≡ y -> y ≡ z -> x ≡ z
x =⟨ y ⟩ z = trans y z

_=⟨⟩_ : {A : Set} -> (x : A) -> {y : A} -> x ≡ y -> x ≡ y
x =⟨⟩ y = x =⟨ refl ⟩ y

```
that's not as useful as i think it is, because i don't know how to match on a function.

let's think about better representations of functions.

```

data Nat : Set where
  zero : Nat
  suc : Nat -> Nat

{-# BUILTIN NATURAL Nat #-}

_+_ : Nat -> Nat -> Nat
zero + n = n
(suc m) + n = m + suc n

_*_ : Nat -> Nat -> Nat
zero * n = zero
(suc m) * n = n + (m * n)

_^_ : Nat -> Nat -> Nat
n ^ zero = 1
n ^ (suc m) = n * (n ^ m)


data List (A : Set) : Set where
  [] : List A
  _::_ : A -> List A -> List A

infix 5 _::_

data _×_ (A B : Set) : Set where
  _,_ : A -> B -> A × B

infix 4 _,_

fst : {A B : Set} -> A × B -> A
fst (a , _) = a

snd : {A B : Set} -> A × B -> B
snd (_ , b) = b

```
one way to represent a function, would be a pair, fst is not var, and snd is var
(false , false)  zero
(false , true )  var
(true  , false)  not
(true  , true )  one

\a f -> where
              false -> fst f
              true  -> snd f

```
apply : Bool -> (Bool × Bool) -> Bool
apply false f = fst f
apply  true f = snd f

compose : (Bool × Bool) -> (Bool × Bool) -> (Bool × Bool)
compose f (false , false) = (fst f , fst f)
compose f (false , true ) = (fst f , snd f)
compose f (true  , false) = (snd f , fst f)
compose f (true  , true ) = (snd f , snd f)

```
so any composition of functions collapses down to a simple pair
```

sn1 : (Bool × Bool)
sn1 = (false , true)
ex1 : (Bool × Bool)
ex1 = compose sn1 (compose sn1 sn1)

```
so what happens with two?

B    0 0 1 1
A    0 1 0 1
------------  |
0  | 0 0 0 0  |
1  | 0 0 0 1  |
2  | 0 0 1 0  |
3  | 0 0 1 1  |
4  | 0 1 0 0  |
5  | 0 1 0 1  |
6  | 0 1 1 0  |
7  | 0 1 1 1  |
8  | 1 0 0 0  |
9  | 1 0 0 1  |
10 | 1 0 1 0  |
11 | 1 0 1 1  |
12 | 1 1 0 0  |
13 | 1 1 0 1  |
14 | 1 1 1 0  |
15 | 1 1 1 1  |

one way, B just selects an A
```
apply2 : Bool -> Bool -> ((Bool × Bool) × (Bool × Bool)) -> Bool
apply2 false false f = fst (fst f)
apply2 false  true f = fst (snd f)
apply2  true false f = snd (fst f)
apply2  true  true f = snd (snd f)

compose2 : ((Bool × Bool) × (Bool × Bool))
        -> ((Bool × Bool) × (Bool × Bool))
        -> ((Bool × Bool) × (Bool × Bool))
compose2 (a1 , a2) (b1 , b2) = ((compose a1 b1) , (compose a2 b2))

```
we should be able to induce more variables, it's just  f × g -> (f × g) × (f x g)

i have lots of swirly ideas about collapsing sub values, and conversion to Nat.

but let's hold off on that for a bit, and try to actually induce n vars.
```

tyn : (n : Nat) -> Set
tyn zero = (Bool × Bool)
tyn (suc n) = ( tyn n ) × ( tyn n )

argn : (n : Nat) -> Set
argn zero = Bool
argn (suc n) = Bool × (argn n)

applyn : (n : Nat) -> tyn n -> argn n -> Bool
applyn zero    f false  =  fst f
applyn zero    f true   =  snd f
applyn (suc n) f (false , rest) = (applyn n (fst f) rest)
applyn (suc n) f (true  , rest) = (applyn n (snd f) rest)

composen : (n : Nat) -> tyn n -> tyn n -> tyn n
composen zero f (false , false) =  fst f , fst f
composen zero f (false , true ) =  fst f , snd f
composen zero f (true  , false) =  snd f , fst f
composen zero f (true  , true ) =  snd f , snd f
composen (suc n) (x1 , y1) (x2 , y2) = (composen n x1 y1) , (composen n x2 y2)

t1 : Bool
t1 = applyn zero (false , true) true
t2 : Bool
t2 = applyn 1 ((false , true),(false , true)) (true , true)

data Bin : Set where
  b  : Bin
  _O : Bin -> Bin
  _I : Bin -> Bin

tb1 : Bin
tb1 = b I I O

inc : Bin -> Bin
inc (x O) = x I
inc (x I) = (inc x) O
inc b     = b I

nattobin : Nat -> Bin
nattobin zero    = b O
nattobin (suc n) = inc (nattobin n)

bintonat : Bin -> Nat
bintonat b = zero
bintonat (x O) = 2 * (bintonat x)
bintonat (x I) = 1 + (2 * (bintonat x))



fntobin : (n : Nat) -> (tyn n) -> Bin
fntobin n f = (kick n f) b
  where
    kick : (n : Nat) -> (tyn n) -> (Bin -> Bin)
    kick  zero  (false , false)  = \ x -> x O O
    kick  zero  (false , true )  = \ x -> x O I
    kick  zero  (true  , false)  = \ x -> x I O
    kick  zero  (true  , true )  = \ x -> x I I
    kick (suc n) (l , r) = left
      where
      right : Bin -> Bin
      right = \ y -> (kick n r) y
      left : Bin -> Bin
      left = \ x -> right ((kick n l) x)


fnt1 : Bin
fnt1 = fntobin 1 ((true , false) , (false , true))
fnt2 : Bin
fnt2 = fntobin 2 (((true , false) , (false , true)),((true , false) , (false , true)))


dropn : Nat -> Bin -> Bin
dropn zero     x    = x
dropn (suc n) (x I) = dropn n x
dropn (suc n) (x O) = dropn n x
dropn (suc n) b     = b

bintofn : (n : Nat) -> Bin -> (tyn n)
bintofn zero (x O O) = (false , false)
bintofn zero (x O I) = (false , true )
bintofn zero (x I O) = (true  , false)
bintofn zero (x I I) = (true  , true )
bintofn zero (x I)   = (false , true )
bintofn zero (x O)   = (false , false)
bintofn zero _ = (false , false)
bintofn (suc n) x = (bintofn n (dropn (2 ^ (suc n)) x) , bintofn n x)

tbf1 : tyn 0
tbf1 = bintofn 0 (nattobin 1)

tbf2 : tyn 1
tbf2 = bintofn 1 (nattobin 1)

tbf3 : tyn 2
tbf3 = bintofn 2 (nattobin 1)

tbf4 : tyn 2
tbf4 = bintofn 2 (nattobin 13)

tbf5 : tyn 4
tbf5 = bintofn 4 (nattobin 13)

nattofn : (n : Nat) -> Nat -> (tyn n)
nattofn n m = bintofn n (nattobin m)


data Expr : Set where
  v_   : Nat -> Expr
  _&&_ : Expr -> Expr -> Expr
  _||_ : Expr -> Expr -> Expr
  ~_   : Expr -> Expr

infix 5 _&&_
infix 4 _||_

te1 : Expr
te1 = v 0

te2 : Expr
te2 = v 0 && v 1

truestack : (n : Nat) -> (tyn n)
truestack 0 = (true , true)
truestack (suc n) = (truestack n , truestack n)
falsestack : (n : Nat) -> (tyn n)
falsestack 0 = (false , false)
falsestack (suc n) = (falsestack n , falsestack n)

exprtofn : (n : Nat) -> Expr -> (tyn n)
exprtofn n (v 0) = (false , true)
exprtofn n (v (suc x)) = (falsestack x , truestack x)
exprtofn n (e && e₁) = {!!}
exprtofn n (e || e₁) = {!!}
exprtofn n (~ e) = {!!}
```
                                       interchange           4! (24) possible column orderings
B    0 0 1 1  |                        A 0 0 1 1  |       |  A 0 0 1 1
A    0 1 0 1  |                        B 0 1 0 1  |       |  B 0 1 0 1
------------  |                      | ---------  |       | ----------
0  | 0 0 0 0  |        0             |   0 0 0 0  |   0   |    0 0 0 0   0
1  | 0 0 0 1  |   a &  b             |   0 0 0 1  |   1   |    1 0 0 0   8
2  | 0 0 1 0  |  ~a &  b             |   0 1 0 0  |   4   |    0 1 0 0   4
3  | 0 0 1 1  |        b             |   0 1 0 1  |   5   |    1 1 0 0  12
4  | 0 1 0 0  |   a & ~b             |   0 0 1 0  |   2   |    0 0 1 0   2
5  | 0 1 0 1  |   a                  |   0 0 1 1  |   3   |    1 0 1 0  10
6  | 0 1 1 0  |  ~a & b | a & ~b     |   0 1 1 0  |   6   |    0 1 1 0   6
7  | 0 1 1 1  |   a | b              |   0 1 1 1  |   7   |    1 1 1 0  14
8  | 1 0 0 0  |  ~ ( a | b )         |   1 0 0 0  |   8   |    0 0 0 1   1
9  | 1 0 0 1  |  a & b | ~( a | b )  |   1 0 0 1  |   9   |    1 0 0 1   9
10 | 1 0 1 0  |  ~ a                 |   1 1 0 0  |  12   |    0 1 0 1   5
11 | 1 0 1 1  |  ~ a  | b            |   1 1 0 1  |  13   |    1 1 0 1  13
12 | 1 1 0 0  |  ~ b                 |   1 0 1 0  |  10   |    0 0 1 1   3
13 | 1 1 0 1  |  a | ~b              |   1 0 1 1  |  11   |    1 0 1 1  11
14 | 1 1 1 0  |  ~ ( a & b )         |   1 1 1 0  |  14   |    0 1 1 1   7
15 | 1 1 1 1  |        1             |   1 1 1 1  |  15   |    1 1 1 1  15

is there a more ineteresting row ordering?
the fastest changing thing is inverses
the slowest changing thing is commute

B    0 0 1 1
A    0 1 0 1
------------  -
0  | 0 0 0 0  |   0 0 1 0 |  2  |  0 1 0 | 0 1 0 |  2
1  | 0 0 0 1  |   1 1 0 1 | 13  |                |

2  | 0 0 1 0  |   0 1 0 0 |  4  |  1 0 0 | 0 1 1 |  3
3  | 0 0 1 1  |   1 0 1 1 | 11  |                |

4  | 0 1 0 0  |   0 1 0 1 |  5  |  1 0 1 | 1 0 0 |  4
5  | 0 1 0 1  |   1 0 1 0 | 10  |                |

6  | 0 1 1 0  |   0 0 1 1 |  3  |  0 1 1 | 1 0 1 |  5
7  | 0 1 1 1  |   1 1 0 0 | 12  |                |

8  | 1 0 0 0  |   0 1 1 0 |  6  |  1 1 0 | 1 1 0 |  6
9  | 1 0 0 1  |   1 0 0 1 |  9  |                |

10 | 1 0 1 0  |   0 0 0 1 |  1  |  0 0 1 | 1 1 1 |  7
11 | 1 0 1 1  |   1 1 1 0 | 14  |                |

12 | 1 1 0 0  |   0 1 1 1 |  7  |  1 1 1 | 0 0 0 |  0
13 | 1 1 0 1  |   1 0 0 0 |  8  |                |

14 | 1 1 1 0  |   0 0 0 0 |  0  |  0 0 0 | 0 0 1 |  1
15 | 1 1 1 1  |   1 1 1 1 | 15  |                |

2 | 0 1 0  ~a . b
3 | 0 1 1    b
4 | 1 0 0  a . ~b
5 | 1 0 1    a
------------------
6 | 1 1 0  xor
7 | 1 1 1  or
0 | 0 0 0  zero
1 | 0 0 1  and


A | 0 1
-------
0 | 0 0
1 | 0 1
2 | 1 0
3 | 1 1

B    0 0 1 1
A    0 1 0 1
------------  |
0  | 0 0 0 0  | 0
1  | 0 0 0 1  | c-
2  | 0 0 1 0  |
3  | 0 0 1 1  | b
4  | 0 1 0 0  |
5  | 0 1 0 1  | a
6  | 0 1 1 0  | c-
7  | 0 1 1 1  | c-
8  | 1 0 0 0  | c-
9  | 1 0 0 1  | c-
10 | 1 0 1 0  | !a
11 | 1 0 1 1  |
12 | 1 1 0 0  | !b
13 | 1 1 0 1  |
14 | 1 1 1 0  | c-
15 | 1 1 1 1  | 1


     \ A|  0    1
    B \ |
    ----------------------
  | 0   |

  | 1   |
