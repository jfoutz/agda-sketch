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

this tutorial is really good. let's finish before jumping back to plfa.

Exercise 2.1. Implement the function downFrom : (n : Nat) → Vec Nat n that, given a number n, produces the vector (n−1)::(n−2):: ... ::0.(You’ll need to copy the definition of the Vec type below to test if your definition typechecks.)

```
data Vec (A : Set) : Nat -> Set where
  []   : Vec A 0
  _::_ : {n : Nat} -> A -> Vec A n -> Vec A (suc n)

downFrom : (n : Nat) -> Vec Nat n
downFrom zero    = []
downFrom (suc n) = n :: (downFrom n)


```
hmm. parameters and indexes.

functions from p12
```
_++Vec_ : { A : Set } {m n : Nat}
        -> Vec A m
        -> Vec A n
        -> Vec A (m + n)

[]        ++Vec ys = ys
(x :: xs) ++Vec ys = x :: (xs ++Vec ys)

head : {A : Set} {n : Nat}
       -> Vec A (suc n)
       -> A
head (x :: xs) = x

```
this here is some magic. Vec must have a count of (suc n) so it's at least 1. no empty list allowed. you can't call it with an empty list, because you have to prove you've got a non empty list to call it.

Exercise 2.2. Implement the function tail : {A : Set}{n : Nat} →
Vec A (suc n) → Vec A n.

```

tail : {A : Set} {n : Nat}
       -> Vec A (suc n)
       -> Vec A n
tail (x :: xs) = xs


last : {A : Set} {n : Nat}
       -> Vec A (suc n)
       -> A
last (x :: []) = x
last (x1 :: x2 :: x3) = last (x2 :: x3)
```

i misread the type for tail, how hard could last be?
agda suggested the triple match. NEAT.

Exercise 2.3. Implement the function dotProduct : {n : Nat} → Vec Nat n → Vec Nat n → Nat that calculates the
‘dot product’ (or scalar product) of two vectors. Note that the type of the function enforces the two vectors to have the same length!

recall, (cause i forgot) dot product multiplies each pair in the vector and sums the result

```
dotProduct : {n : Nat}
             -> Vec Nat n
             -> Vec Nat n
             -> Nat

dotProduct [] [] = 0
dotProduct (x :: xs) (y :: ys) = (x * y) + (dotProduct xs ys)

```
fin. hmm. i've made some half hearted attempts at making use of Fin n, saturation vs overflow arithmatic. i never quite figured out how to juggle the 2 values and decide when to cap the result or overflow the result.

```
data Fin : Nat -> Set where
  zero : {n : Nat} -> Fin (suc n)
  suc  : {n : Nat} -> Fin n -> Fin (suc n)

lookupVec : {A : Set} {n : Nat} -> Vec A n -> Fin n -> A
lookupVec (x :: xs) zero    = x
lookupVec (x :: xs) (suc i) = lookupVec xs i

v : Vec Nat 3
v = 1 :: 2 :: 3 :: []

t1 : Nat
t1 = lookupVec v (suc (suc zero))
-- 3

t2 : Nat
t2 = lookupVec v zero
-- 1

```
Exercise 2.4.
putVec : {A : Set}{n : Nat} →
Fin n → A → Vec A n → Vec A n that sets the value at the given position in the vector to the given value,
and leaves the rest of the vector unchanged.

```

putVec : {A : Set}{n : Nat}
         -> Fin n
         -> A
         -> Vec A n
         -> Vec A n
putVec zero    a (x :: xs) = a :: xs
putVec (suc n) a (x :: xs) = x :: putVec n a xs

t3 : Vec Nat 3
t3 = putVec (suc zero) 5 v

```
_s+_ : {n : Nat}
       -> Fin n
       -> Fin n
       -> Fin n

zero   s+ b = b
suc  a s+ b = ?

i still don't know how to pattern match to check if b is full.
someday, Fin. someday.
```

data Σ (A : Set) (B : A -> Set) : Set where
  _,_ : (x : A) -> B x -> Σ A B

_×'_ : (A B : Set) -> Set
A ×' B = Σ A (\ _ -> B)

```
there's a lot going on here.
the type of B is a function, it takes an A and returns a Set. a type.
i'm mixing layers here. examples will help.

```
fstΣ : {A : Set}{B : A -> Set} -> Σ A B -> A
fstΣ (x , y) = x

sndΣ : {A : Set}{B : A -> Set} -> (z : Σ A B) -> B (fstΣ z)
sndΣ (x , y) = y

List' : (A : Set) -> Set
List' A = Σ Nat (Vec A)

```
xercise2.6. Implementfunctions converting back and forth between List A and List’ A. Hint. First define the functions []’ : {A : Set} → List’ A and _::’_ : {A : Set} → A → List’ A → List’ A.

The hint is a good hint.

what's the base case? ( whatever, (\ _ -> []) )?
like, if i need to use a flag to indicate the end, i want to pick a good flag. [] seems lame.

we've got maybe.

i guess, if A's are all maybe A, b could be a simple function matching on just/nothing.
that's kinda goofy, because we've already got the pair.

[1,2,3] -> (1,(2,3))
but, what's the empty list?
[] -> (?,?)

There is a temptation to use something like \ _ -> Fin 0, but that's at the type level. and i can't construct a value.

I guess my only option is to take a lispy apprach, and add a nil

data Nil : Set where
  nil : Nil

this won't work because the types don't agree.

[]' : {A : Set} -> List' A
[]' = nil

OH.

List' A = Σ Nat (Vec A)

we're not stacking pairs like cons cells. we're tucking away the length in a pair.
list -> vector, not list -> ( , (, (...)) )

much much easier.
```
[]' : {A : Set} -> List' A
[]' = (0 , [])

_::'_ : {A : Set} -> A -> List' A -> List' A
x ::' (l , v) = (suc l , x :: v )

l->l' : {A : Set} -> List A -> List' A
l->l' []        = []'
l->l' (x :: xs) = x ::' (l->l' xs)

l'->l : {A : Set} -> List' A -> List A
l'->l (0 , _) = []
l'->l ( (suc a) , x :: xs ) = x :: (l'->l (a , xs))

l1 : List Nat
l1 = 1 :: 2 :: 3 :: []

l2 : List' Nat
l2 = l->l' l1

l3 : List Nat
l3 = l'->l l2


```
wow that was a bunch of rabbit holes.

neat.


Conjunction, P and Q (p , q) - a pair
Implication, P implies Q, p -> q - a function, which is still amazing.
Disjunction, P or Q left p or right q - the Either type

Define the Either type in Agda, and write down a definition of thefunctioncases:{ABC:Set}→ Either AB→(A→C)→(B→C)→ C.

```
data Either (A B : Set) : Set where
  left  : A -> Either A B
  right : B -> Either A B

cases : { A B C : Set } -> Either A B -> (A -> C) -> (B -> C) -> C
cases (left a)  f _ = f a
cases (right b) _ g = g b

data ⊤ : Set where
  tt : ⊤

data ⊥ : Set where

absurd : {A : Set} -> ⊥ -> A
absurd ()


```
Translatethefollowing propositions to Agda types using the Curry-Howard correspondence, and prove them by implementing a function of that type.
• If A then (B implies A).
• If ( A and true) then ( A or false).
• If A implies (B implies C), then (A and B) implies C.
    not exactly sure how to parse this one, so there are a few
• IfAand(BorC),theneither(A and B) or (A and C).
• If A implies C and B implies D, then (A and B) implies (C and D).

```
p1 : { A B : Set } -> A -> (B -> A)
p1 a = \ _ -> a

p2 : { A : Set } -> (A × ⊤) -> Either A ⊥
p2 ( a , _ ) = left a

p3 : { A B C : Set } -> (A -> (B -> C)) -> ((A × B) -> C)
p3 f = \ { (a , b) -> f a b }

p3a : { A B C : Set } -> A -> (B -> C) -> (A × B) -> C
p3a a f (_ , b) = f b

-- this is probably the intention for 3
p3b : { A B C : Set } -> (A -> (B -> C)) -> (A × B) -> C
p3b  f (a , b) = f a b

p4 : {A B C : Set} -> (A × Either B C) -> Either (A × B) (A × C)
p4 (a , left b)  = left (a , b)
p4 (a , right c) = right (a , c)

p5 : {A B C D : Set} -> (A -> C) -> (B -> D) -> (A × B) -> (C × D)
p5 f g (a , b) = (f a , g b)

p5a : {A B C D : Set} -> (A -> C) -> (B -> D) -> ((A × B) -> (C × D))
p5a f g = \ { (a , b) -> (f a , g b) }

```

double negation. hmm.

Exercise 3.3. Write a function of type {P : Set} → (Either P (P → ⊥) → ⊥) → ⊥.
```

ex3 : {P : Set} -> (Either P (P -> ⊥) -> ⊥) -> ⊥
ex3 = λ z → z (right (λ x → z (left x)))

```
i spent quite a bit of time thinking about and delaying attempting ex3.3
finally gave in and took advantage of autosolve.

there is a hole in my understanding.
ex3a : {P : Set} -> (P -> ⊥) -> ⊥
ex3a f = \p -> f p

i don't know how to connect the dots that f can't exist.
if you can give me an (P -> ⊥), you're a liar.
it seems like when i call f with p, that would typecheck to ⊥
and meet the spec.

but no. i must be relying on something i don't understand.
ex3b : {P : Set} -> (Either P (P -> ⊥) -> ⊥) -> ⊥
ex3b f = help where
  help : {P : Set} -> Either P (P -> ⊥)
  help (left x) = ?
  help (right x) = ?

ok, P implies ⊥ is false, first, we've got p which is obviously not ⊥. Furthermore, there's no way to get a ⊥.

still fuzzy. mixing proposition and proof layers.

it is not the case that P implies ⊥.

ex3b : {P : Set}
      -> (Either
             P        -- we've got a proof
             (P -> ⊥)) -- we've got a proof that implies ⊥
      -> ⊥ -- is false
ex3b (left p) = p


alright, these are lecture notes.
ex3c : {P : Set} -> (Either P (P -> ⊥) -> ⊥) -> ⊥
there must be a walkthrough of this in the class.

either a b implies false is false.

i think the idea here, and what agda gave me, is a counter example to

either a b implies false

there must be a bunch of absurd cases.
```
ex3c : {P : Set} -> (Either P (P -> ⊥) -> ⊥) -> ⊥
ex3c = \ z -> z (right (\ x -> z (left x)))

ex3ch : (Either Nat (Nat -> Nat) -> Nat)
ex3ch (left n) = n
ex3ch (right f) = f zero
```
so this is cheating, of course, because we know a Nat. P can be anything,
so we can't provide a simple value.
ex3c = \ z -> z
      (right
         (\ x -> z (left x)))

call z, with a right, who's value is a lambda.

ex3ch2 : {P : Set} -> (Either P (P -> Nat) -> Nat)
ex3ch2 = \ z -> {!!}
^ won't work.

i need to decode which P is the counterexample
ex3c : {P : Set} -> (Either P (P -> ⊥) -> ⊥) -> ⊥
ex3c = \ z -> z (right (\ x -> z (left x)))

 this - (\ x -> z (left x)) seems to say, give me an x, and i'll give you a function
 that takes an X, and returns ⊥.
ex3c = \ z -> z (right (\ x -> z (left x)))

i don't get it.
ccc : Either ⊤ (⊤ -> ⊥)
ccc = right tt

⊤ !=< (⊤ → ⊥)
when checking that the expression tt has type ⊤ → ⊥

ccc : Either ⊤ (⊤ -> ⊥)
ccc = {!!}
?0 : Either ⊤ (⊤ → ⊥)

ex3c = \ z -> z (right (\ x -> z (left x)))
ex3c = \ z -> (right (\ x -> z (left x))) (right (\ x -> (right (\ x -> z (left x))) (left x)))

!!! think harder.
```

data IsEven : Nat -> Set where
  zeroIsEven : IsEven zero
  sucsucIsEven : {n : Nat} -> IsEven n -> IsEven (suc (suc n))

6-is-even : IsEven 6
6-is-even = sucsucIsEven ( sucsucIsEven (sucsucIsEven zeroIsEven) )

7-is-not-even : IsEven 7 -> ⊥
7-is-not-even (sucsucIsEven (sucsucIsEven (sucsucIsEven ())))

data IsTrue : Bool -> Set where
  TrueIsTrue : IsTrue true

_=Nat_ : Nat -> Nat -> Bool
zero    =Nat    zero = true
(suc x) =Nat (suc y) = x =Nat y
_       =Nat       _ = false

length-is-3 : IsTrue (length (1 :: 2 :: 3 :: []) =Nat 3)
length-is-3 = TrueIsTrue


double : Nat -> Nat
double zero = zero
double (suc n) = suc (suc (double n))

double-is-even : (n : Nat) -> IsEven (double n)
double-is-even zero = zeroIsEven
double-is-even (suc m) = sucsucIsEven (double-is-even m)

n-equals-n : (n : Nat) -> IsTrue (n =Nat n)
n-equals-n zero = TrueIsTrue
n-equals-n (suc m) = n-equals-n m

half-a-dozen : Σ Nat (\ n -> IsTrue ((n + n) =Nat 12))
half-a-dozen = 6 , TrueIsTrue

zero-or-suc : (n : Nat)
  -> Either (IsTrue (n =Nat 0))
            (Σ Nat (\ m -> IsTrue (n =Nat (suc m))))

zero-or-suc zero = left TrueIsTrue
zero-or-suc (suc m) = right (m , n-equals-n m)

data _≡_ {A : Set} : A -> A -> Set where
  refl : {x : A} -> x ≡ x

infix 4 _≡_

one-plus-one : 1 + 1 ≡ 2
one-plus-one = refl

zero-not-one : 0 ≡ 1 -> ⊥
zero-not-one ()

id-returns-input : { A : Set } -> (x : A) -> id x ≡ x
id-returns-input x = refl

sym : {A : Set} {x y : A} -> x ≡ y -> y ≡ x
sym refl = refl

trans : {A : Set} {x y z : A} -> x ≡ y -> y ≡ z -> x ≡ z
trans refl refl = refl

cong : {A B : Set} {x y : A} -> (f : A -> B) -> x ≡ y -> f x ≡ f y
cong f refl = refl

begin_ : {A : Set} -> {x y : A} -> x ≡ y -> x ≡ y
begin p = p

_end : {A : Set} -> (x : A) -> x ≡ x
x end = refl

_=⟨_⟩_ : { A : Set } -> (x : A) -> {y z : A}
         -> x ≡ y -> y ≡ z -> x ≡ z
x =⟨ y ⟩ z = trans y z

_=⟨⟩_ : {A : Set} -> (x : A) -> {y : A} -> x ≡ y -> x ≡ y
x =⟨⟩ y = x =⟨ refl ⟩ y

infix  1 begin_
infix  3 _end
infixr 2 _=⟨_⟩_
infixr 2 _=⟨⟩_

[_]   : {A : Set} -> A -> List A
[ x ] = x :: []

reverse : {A : Set} -> List A -> List A
reverse []        = []
reverse (x :: xs) = reverse xs ++ [ x ]

reverse-singleton : {A : Set} (x : A) -> reverse [ x ] ≡ [ x ]
reverse-singleton x =
  begin
    reverse [ x ]
  =⟨⟩
    reverse (x :: [])
  =⟨⟩
    reverse [] ++ [ x ]
  =⟨⟩
    [] ++ [ x ]
  =⟨⟩
    [ x ]
  end

not-not : (b : Bool) -> not (not b) ≡ b
not-not false =
  begin
    not (not false)
  =⟨⟩
    not true
  =⟨⟩
    false
  end
not-not true =
  begin
    not (not true)
  =⟨⟩
    not false
  =⟨⟩
    true
  end

add-n-zero : (n : Nat) -> n + zero ≡ n
add-n-zero zero =
  begin
    zero + zero
  =⟨⟩
    zero
  end
add-n-zero (suc n) =
  begin
    (suc n) + zero
  =⟨⟩
    suc (n + zero)
  =⟨ cong suc (add-n-zero n) ⟩
    suc n
  end

```
Exercise 4.1. Prove that m + suc n = suc (m + n) for all natural numbers m and n. Next, use the previous lemma and this one to prove commutativity of addition, i.e. that m + n = n + m for all natural numbers m and n.



add-m-n : (m n : Nat) -> m + (suc n) ≡ suc (m + n)
add-m-n zero n =
  begin
    zero + (suc n)
  =⟨⟩
    zero + (suc (zero + n))
  =⟨⟩
    (suc (zero + n))
  end
add-m-n m n =
  begin
    m + (suc n)
  =⟨ cong suc ( \ i -> add-m-n i n ) ⟩
    suc (m + n)
  _end


```
add-0-n : (n : Nat) -> 0 + (suc n) ≡ suc (0 + n)
add-0-n n =
  begin
    0 + (suc n)
  =⟨⟩
    (suc n)
  =⟨⟩
    suc (0 + n)
  end

add-1-n : (n : Nat) -> 1 + (suc n) ≡ suc (1 + n)
add-1-n n =
  begin
    1 + (suc n)
  =⟨⟩
    suc (suc n)
  =⟨⟩
    suc (1 + n)
  end

add-2-n : (n : Nat) -> 2 + (suc n) ≡ suc (2 + n)
add-2-n n =
  begin
    2 + (suc n)
  =⟨⟩
    (suc (suc (suc n)))
  =⟨⟩
    suc (2 + n)
  end

add-m-n : (m n : Nat) -> m + (suc n) ≡ suc (m + n)
add-m-n zero n =
  begin
    0 + (suc n)
  =⟨⟩
    suc n
  =⟨⟩
    suc (0 + n)
  end
add-m-n (suc m) n =
  begin
    (suc m) + (suc n)
  =⟨ cong suc (add-m-n m n) ⟩
    suc (suc (m + n))
  end
  ```
  i think maybe i went about this in a really strange way.
  i think the hint was about operating on n not m.
  writing down examples was spectacularly helpful.

add-m-n' : (m n : Nat) -> m + (suc n) ≡ suc (m + n)
add-m-n' m zero =
  begin
    m + (suc zero)
  =⟨⟩
    m + 1
  =⟨⟩ --------- this part fails because + reduces it's first argument
  --------- sorta have to work on the left, not the right.
    (suc m)
  =⟨⟩
    suc (m + zero)
  end

add-m-n' m (suc n) = ?
maybe i did do it right

add-n-zero : (n : Nat) -> n + zero ≡ n
```

comm0+1 : 0 + 1 ≡ 1 + 0
comm0+1 =
  begin
    0 + 1
  =⟨⟩
    1
  =⟨⟩
    1 + 0
  end

comm1+2 : 1 + 2 ≡ 2 + 1
comm1+2 =
  begin
    1 + 2
  =⟨⟩
    3
  =⟨⟩
    2 + 1
  end

comm+ : (m n : Nat) -> m + n ≡ n + m
comm+ m zero =
  begin
    m + zero
  =⟨ add-n-zero m ⟩
    m
  =⟨⟩
    zero + m
  end
comm+ m (suc n) =
  begin
    m + (suc n)
  =⟨ add-m-n m n ⟩
    suc (m + n)
  =⟨ cong suc (comm+ m n) ⟩
    suc (n + m)
  =⟨⟩
    (suc n) + m
  end

```
whew. ok.
two big lessons.


  =⟨ you can put functions here⟩

which is super cool

  =⟨ cong f-incr induction ⟩

which is even cooler.

i wonder about the extracted code. i suspect everything before the cong is before  the recursive call, and everything after is on the stack. There's a list example coming up with an accumulator. that'll be interesting.

anywho.

```

add-assoc : (x y z : Nat) -> x + (y + z) ≡ (x + y) + z
add-assoc zero y z =
  begin
    zero + (y + z)
  =⟨⟩
    y + z
  =⟨⟩
    (zero + y) + z
  end
```
so, this works, and i'm not sure why.
add-assoc (suc x) y z =
  begin
    (suc x) + (y + z)
  =⟨ cong suc (add-assoc x y z) ⟩
    ((suc x) + y) + z
  end

book answer:
```
add-assoc (suc x) y z =
  begin
    (suc x) + (y + z)
  =⟨⟩
    suc (x + (y + z))
  =⟨ cong suc (add-assoc x y z) ⟩
    suc ((x + y) + z)
  =⟨⟩
    (suc (x + y)) + z
  =⟨⟩
    ((suc x) + y) + z
  end

```
i think moving suc around might be part of nat search.
but maybe it's just part of +. who knows.

Exercise4.2. Considerthefollowing function:
replicate : {A : Set} → Nat → A → List A
replicate zero x = [] (64) replicate (suc n) x =
x :: replicate n x

Prove that the length of replicate n x is always equal to n, by induction on the number n.
```

replicate : { A : Set } -> Nat -> A -> List A
replicate zero x    = []
replicate (suc n) x = x :: replicate n x

replicate-n-len : { A : Set } -> (n : Nat) -> (x : A) -> length (replicate n x) ≡ n
replicate-n-len zero x =
  begin
    length (replicate zero x)
  =⟨⟩
    length []
  =⟨⟩
    zero
  end
replicate-n-len (suc n) x =
  begin
    length (replicate (suc n) x)
  =⟨ cong suc (replicate-n-len n x) ⟩
    (suc n)
  end
```

neat.

reverse. where block
```

reverse-reverse : {A : Set} -> (xs : List A) -> reverse (reverse xs) ≡ xs

reverse-reverse [] =
  begin
    reverse (reverse [])
  =⟨⟩
    reverse []
  =⟨⟩
    []
  end
reverse-reverse (x :: xs) = {!!}
