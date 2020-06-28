module Combinators where

open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Agda.Primitive
open import Agda.Builtin.Bool
open import Agda.Builtin.Equality
open import Agda.Builtin.Sigma
  renaming (fst to proj₁; snd to proj₂)
    hiding (module Σ)
module Σ = Agda.Builtin.Sigma.Σ
  renaming (fst to proj₁; snd to proj₂)
open import Agda.Builtin.Unit

foldℕ : {r : Set} → r → (r → r) → (n : ℕ) → r
foldℕ z _ zero = z
foldℕ z s (suc n) = s (foldℕ z s n)

infix 0 _≃_
record _≃_ (A B : Set) : Set where
  field
    to         : A → B
    from       : B → A
    from∘to≡id : ∀ x → from (to x) ≡ x
    to∘from≡id : ∀ y → to (from y) ≡ y

open _≃_  {{...}}

infix 0 _↔_
record _↔_ (A B : Set) : Set where
  field
    to         : A → B
    from       : B → A

open _↔_  {{...}}

infixr 0 _$_
_$_ : {A B : Set} → (A → B) → A → B
f $ x = f x

infixr 9 _∘_
_∘_ : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c}
    → (B → C) → (A → B) → (A → C)
(f ∘ g) x = f (g x)

id : ∀ {a} {A : Set a} → A → A
id x = x

flip : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c}
     → (A → B → C) → B → A → C
flip f a b = f b a

const : ∀ {a b} {A : Set a} {B : Set b} → A → B → A
const x _ = x

data Maybe (A : Set) : Set where
  nothing : Maybe A
  just    : A → Maybe A

maybe : {A B : Set} → B → (A → B) → Maybe A → B
maybe def _ nothing = def
maybe _   f (just x) = f x

data ⊥ : Set where

infix 3 ¬_

¬_ : Set → Set
¬ p = p → ⊥

-- TODO use Dec from stdlib
data Dec (P : Set) : Set where
  yes : ( p :   P) → Dec P
  no  : (¬p : ¬ P) → Dec P

foldDec : {P R : Set} → (P → R) → (¬ P → R) → Dec P → R
foldDec fʸ fⁿ (yes p) = fʸ p
foldDec fʸ fⁿ (no ¬p) = fⁿ ¬p

infix 2 Σ-syntax

Σ-syntax : ∀ {a b} (A : Set a) → (A → Set b) → Set (a ⊔ b)
Σ-syntax = Σ

syntax Σ-syntax A (λ x → B) = Σ[ x ∈ A ] B

infixr 2 _×_

_×_ : ∀ {a b} (A : Set a) → (B : Set b) → Set (a ⊔ b)
A × B = Σ[ _ ∈ A ] B

∃ : ∀ {a b} {A : Set a} → (A → Set b) → Set (a ⊔ b)
∃ = Σ _

∃-syntax : ∀ {a b} {A : Set a} → (A → Set b) → Set (a ⊔ b)
∃-syntax = ∃

syntax ∃-syntax (λ x → B) = ∃[ x ] B

infix 4 -,_

-,_ : ∀ {a b} {A : Set a} {B : A → Set b} {x} → B x → ∃ B
-, y = _ , y

curry : ∀ {a b c} {A : Set a} {B : A → Set b} {C : Σ A B → Set c}
      → (∀ p → C p) → ∀ x y → C (x , y)
curry f x y = f (x , y)

uncurry : ∀ {a b c} {A : Set a} {B : A → Set b}
          {C : Σ A B → Set c}
        → (∀ x y → C (x , y)) → ∀ p → C p
uncurry f (x , y) = f x y

infixr 1 _⊎_

data _⊎_ (A B : Set) : Set where
  inj₁ : A → A ⊎ B
  inj₂ : B → A ⊎ B

[_,_] : {A B C : Set} → (A → C) → (B → C) → A ⊎ B → C
[ f , _ ] (inj₁ a) = f a
[ _ , g ] (inj₂ b) = g b

map₁ : {A B C : Set} → (A → C) → A ⊎ B → C ⊎ B
map₁ f = [ inj₁ ∘ f , inj₂ ]

map₂ : {A B C : Set} → (B → C) → A ⊎ B → A ⊎ C
map₂ f = [ inj₁ , inj₂ ∘ f ]

record RawFunctor {ℓ} (F : Set ℓ → Set)
  : Set (lsuc ℓ) where
  infixl 4 _<$>_
  infixl 4 _<&>_

  field
    _<$>_ : {A B : Set ℓ} → (A → B) → F A → F B

  _<&>_ : {A B : Set ℓ} → F A → (A → B) → F B
  _<&>_ = flip _<$>_

record RawInvariant {ℓ : Level} (F : Set ℓ → Set)
  : Set (lsuc ℓ) where
  field
    invmap : {A B : Set ℓ} → (A → B) → (B → A) → F A → F B

record RawBifunctor {ℓ : Level} (F : Set ℓ → Set ℓ → Set)
  : Set (lsuc ℓ) where
  field
    bimap : {A B C D : Set ℓ}
          → (A → C) → (B → D) → F A B → F C D

record RawApplicative {ℓ : Level} (F : Set ℓ → Set)
  : Set (lsuc ℓ) where
  infixl 4 _⊛_ _<*>_

  field
    pure : {A : Set ℓ} → A → F A
    _⊛_ : {A B : Set ℓ} → F (A → B) → F A → F B
    {{applicativeFunctor}} : RawFunctor F

  _<*>_ : {A B : Set ℓ} → F (A → B) → F A → F B
  _<*>_ = _⊛_

record RawMonad {ℓ : Level} (M : Set ℓ → Set)
  : Set (lsuc ℓ) where
  infixl 1 _>>=_
  infixr 1 _=<<_

  field
    _>>=_ : {A B : Set ℓ} → M A → (A → M B) → M B
    {{monadApplicative}} : RawApplicative M

  _=<<_ : {A B : Set ℓ} → (A → M B) → M A → M B
  _=<<_ = flip _>>=_

open RawFunctor {{...}}
open RawInvariant {{...}}
open RawBifunctor {{...}}
open RawApplicative {{...}}
open RawMonad {{...}}

instance
  MaybeFunctor : RawFunctor Maybe
  MaybeFunctor = record
    { _<$>_ = maybe nothing ∘ (just ∘_)
    }

instance
  ProductFunctor : {A : Set} → RawFunctor (A ×_)
  ProductFunctor = record
    { _<$>_ = λ f (l , r) → (l , f r)
    }

instance
  SumFunctor : {A : Set} → RawFunctor (A ⊎_)
  SumFunctor = record
    { _<$>_ = [ inj₁ ,_] ∘ (inj₂ ∘_)
    }

instance
  FunctionFunctor : {A : Set} → RawFunctor (λ B → (A → B))
  FunctionFunctor = record
    { _<$>_ = _∘_
    }

instance
  SumBifunctor : RawBifunctor _⊎_
  SumBifunctor = record
    { bimap = λ f g → [ inj₁ ∘ f , inj₂ ∘ g ]
    }

instance
  SumApplicative : {A : Set} → RawApplicative (A ⊎_)
  SumApplicative = record
    { pure = inj₂
    ; _⊛_ = λ ff fx → [ inj₁ , _<$> fx ] ff
    }

instance
  FunctionApplicative : {A : Set}
                      → RawApplicative (λ B → (A → B))
  FunctionApplicative = record
    { pure = const
    ; _⊛_ = λ f g x → f x (g x)
    }

instance
  SumMonad : {A : Set} → RawMonad (A ⊎_)
  SumMonad = record
    { _>>=_ = flip [ inj₁ ,_]
    }

data SK : Set where
  S : SK
  K : SK
  _`_ : SK → SK → SK

infixl 2 _`_

pattern I = S ` K ` K
pattern C = S ` (S ` (K ` (S ` (K ` S) ` K)) ` S) ` (K ` K)
pattern B = S ` (K ` S) ` K
pattern W = S ` S ` (S ` K)
-- Note: Y combinator is not in normal form
pattern Y = S ` S ` K ` (S ` (K ` (S ` S ` (S ` (S ` S ` K)))) ` K)

-- These are in normal form, see ℕasSKfixpoint
pattern skZero = K ` (S ` K ` K)
pattern skSuc  = S ` (S ` (K ` S) ` K)

-- This type mostly exists because it's necessary for the
-- definition of reductions, otherwise reducibility could be
-- defined in terms of the existence of a reduction
data Reducible : (x : SK) → Set where
  redK  : ∀ x y   → Reducible (K ` x ` y)
  redS  : ∀ x y z → Reducible (S ` x ` y ` z)
  red`ˡ : ∀ x y   → Reducible x → Reducible (x ` y)
  red`ʳ : ∀ x y   → Reducible y → Reducible (x ` y)

infix 1 _-[_]→_
infix 1 _-[]→_

-- Reduction: x can be reduced to y in exactly n steps
data _-[_]→_ : (x : SK) → (steps : ℕ) → (y : SK) → Set where
  equal : ∀ {x} 
        → x -[ zero ]→ x
  K-step : ∀ {x y z n} 
         → x -[ n ]→ z
         → K ` x ` y -[ suc n ]→ z
  S-step : ∀ {x y z w n}
         → x ` z ` (y ` z) -[ n ]→ w
         → S ` x ` y ` z -[ suc n ]→ w
  `-stepˡ : ∀ {x x' y n}
          → x -[ suc n ]→ x'
          → x ` y -[ suc n ]→ x' ` y
  `-stepʳ : ∀ {x y y' n}
          → y -[ suc n ]→ y'
          -- → ¬ ∃[ x' ] ∃[ m ] (x -[ suc m ]→ x') -- doesn't work
          → ¬ Reducible x                -- so we use this instead
          → x ` y -[ suc n ]→ x ` y'

-- x can be reduced to y in some number of steps
-- note that this number could be zero, so this does not
-- imply reducibility
_-[]→_ : SK → SK → Set
x -[]→ y = ∃[ n ] (x -[ n ]→ y)

reducible? : ∀ x → Dec (Reducible x)
reducible? S = no λ ()
reducible? K = no λ ()
reducible? (S ` y) with reducible? y
... | yes p = yes (red`ʳ S y p)
... | no ¬p = no λ where (red`ʳ .S .y p) → ¬p p
reducible? (K ` y) with reducible? y
... | yes p = yes (red`ʳ K y p)
... | no ¬p = no λ where (red`ʳ .K .y p) → ¬p p
reducible? (S ` x ` y) with reducible? x
... | yes p = yes (red`ˡ (S ` x) y (red`ʳ S x p))
... | no ¬p with reducible? y
...   | yes q = yes (red`ʳ (S ` x) y q)
...   | no ¬q = no λ where
  (red`ˡ .(S ` x) .y (red`ʳ .S .x p)) → ¬p p
  (red`ʳ .(S ` x) .y p) → ¬q p
reducible? (K ` x ` y) = yes (redK x y)
reducible? (S ` y ` z ` w) = yes (redS y z w)
reducible? (K ` y ` z ` w) = yes (red`ˡ (K ` y ` z) w (redK y z))
reducible? (x ` y ` z ` w ` u) with reducible? (x ` y ` z ` w)
... | yes p = yes (red`ˡ (x ` y ` z ` w) u p)
... | no ¬p with reducible? u
...   | yes q = yes (red`ʳ (x ` y ` z ` w) u q)
...   | no ¬q = no λ where
  (red`ˡ .(x ` y ` z ` w) .u p) → ¬p p
  (red`ʳ .(x ` y ` z ` w) .u p) → ¬q p

Reducible↔Reduction
  : ∀ {x} → Reducible x ↔ ∃[ n ] ∃[ y ] (x -[ suc n ]→ y)
Reducible↔Reduction = record
  { to = t
  ; from = f
  }
  where
    t : ∀ {x} → Reducible x → ∃[ n ] ∃[ y ] (x -[ suc n ]→ y)
    t (redK x y) = zero , x , K-step equal
    t (redS x y z) = zero , (x ` z ` (y ` z)) , S-step equal
    t (red`ˡ x y p) with t p
    ... | n' , x' , q = n' , (x' ` y) , `-stepˡ q
    t (red`ʳ x y p) with t p | reducible? x
    ... | n' , x' , q | no ¬r = n' , (x ` x') , `-stepʳ q ¬r
    ... | n' , x' , q | yes r with t r
    ...   | n'' , x'' , s = n'' , (x'' ` y) , `-stepˡ s

    f : ∀ {x} → ∃[ n ] ∃[ y ] (x -[ suc n ]→ y) → Reducible x
    f (n , _ , K-step {x} {y} p) = redK _ _
    f (n , _ , S-step {x} {y} {z} p) = redS x y z
    f (n , (_ ` y) , `-stepˡ p) = red`ˡ _ _ (f (-, (-, p)))
    f (n , .(_ ` _) , `-stepʳ p _) = red`ʳ _ _ (f (-, (-, p)))

-- TODO (p q : x -[ n ]→ y) → p ≡ q

----------------------

--n-Reducible : ℕ → SK → Set
--n-Reducible n x = ∃[ x' ] (x -[ n ]→ x')

--Reducible : SK → Set
--Reducible = n-Reducible 1

--reducible? : ∀ x → Dec (Reducible x)
--reducible? S = no λ ()
--reducible? K = no λ ()
--reducible? (S ` x) with reducible? x
--... | yes (x' , p) = yes ((S ` x') , `-stepʳ p)
--... | no ¬p = no λ where (_ , `-stepʳ {y' = y'} p) → ¬p (y' , p)
--reducible? (K ` x) with reducible? x
--... | yes (x' , p) = yes ((K ` x') , `-stepʳ p)
--... | no ¬p = no λ where (_ , `-stepʳ {y' = y'} p) → ¬p (y' , p)
--reducible? (S ` x ` y) with reducible? x
--... | yes (x' , p) = yes ((S ` x' ` y) , `-stepˡ (`-stepʳ p))
--... | no ¬p with reducible? y
--...   | yes (y' , q) = yes ((S ` x ` y') , `-stepʳ q)
--...   | no ¬q = no λ where
--  (.(S ` _ ` y) , `-stepˡ (`-stepʳ {y' = y'} p)) → ¬p (y' , p)
--  (.(S ` x ` _) , `-stepʳ {y' = y'} p) → ¬q (y' , p)
--reducible? (K ` x ` y) = yes (x , K-step equal)
--reducible? (S ` y ` z ` w) =
--  yes ((y ` w ` (z ` w)) , S-step equal)
--reducible? (K ` x ` y ` z) =
--  yes ((x ` z) , `-stepˡ (K-step equal))
--reducible? (x ` y ` z ` w ` u) with reducible? (x ` y ` z ` w)
--... | yes (xyzw' , p) = yes ((xyzw' ` u) , `-stepˡ p)
--... | no ¬p with reducible? u
--...   | yes (u' , q) = yes ((x ` y ` z ` w ` u') , `-stepʳ q)
--...   | no ¬q = no λ where
--  (.(_ ` u) , `-stepˡ {x' = x'} p) → ¬p (x' , p)
--  (.(x ` y ` z ` w ` _) , `-stepʳ {y' = y'} p) → ¬q (y' , p)

--sucnReducible↔Reducible :
--  ∀ x → ∃[ n ] n-Reducible (suc n) x ↔ Reducible x
--sucnReducible↔Reducible x = record
--  { to = t x
--  ; from = zero ,_
--  }
--  where
--    t : ∀ x
--      → ∃[ n ] ∃[ z ] (x -[ suc n ]→ z) → ∃[ y ] (x -[ 1 ]→ y)
--    t x (n , z , K-step {x = x'} p) = x' , K-step equal
--    t x (n , z , S-step {x = x'} {y = y'} {z = z'} p) =
--      (x' ` z' ` (y' ` z')) , S-step equal
--    t x (n , .(_ ` _) , `-stepˡ {y = y} p) with t _ (-, -, p)
--    ... | y' , q = (y' ` y) , `-stepˡ q
--    t x (n , .(_ ` _) , `-stepʳ {x = x'} p) with t _ (-, -, p)
--    ... | y' , q = (x' ` y') , `-stepʳ q

---- weakenReducibility : ∀ {n m x}
----                    → n-Reducible (m + n) x → n-Reducible n x
---- weakenReducibility p = {!   !}

--n+0≡n : ∀ n → n + 0 ≡ n
--n+0≡n zero = refl
--n+0≡n (suc n) rewrite n+0≡n n = refl

--reduce-trans
--  : ∀ {x z n m}
--  → ∃[ y ] ((x -[ n ]→ y) × (y -[ m ]→ z)) ↔ x -[ n + m ]→ z
--reduce-trans = record
--  { to = ?
--  ; from = ?
--  }
--  where
--    -- t : ∀ {x z n m}
--    --   → ∃[ y ] ((x -[ n ]→ y) × (y -[ m ]→ z)) → x -[ n + m ]→ z
--    -- t (y , equal , q) = q
--    -- t (y , K-step p , q) = K-step (t (y , (p , q)))
--    -- t (y , S-step p , q) = S-step (t (y , (p , q)))
--    -- t (.(_ ` _) , `-stepˡ p , q) = {!   !}
--    -- t (.(_ ` _) , `-stepʳ p , q) = {!   !}
--    f : ∀ {x z n m}
--      → x -[ n + m ]→ z → ∃[ y ] ((x -[ n ]→ y) × (y -[ m ]→ z))
--    f {x} {n = zero} p = x , equal , p
--    f {n = suc n} (K-step p) = {!   !}
--    f {n = suc n} (S-step p) = {!   !}
--    f {n = suc n} (`-stepˡ p) = {!   !}
--    f {n = suc n} (`-stepʳ p) = {!   !}

---- reduce-trans-to
----   : ∀ {x y z n m}
----   → ((x -[ n ]→ y) × (y -[ m ]→ z)) → x -[ n + m ]→ z
---- reduce-trans-to (equal , q) = q
---- reduce-trans-to (K-step p , q) = K-step (reduce-trans-to (p , q))
---- reduce-trans-to (S-step p , q) = S-step (reduce-trans-to (p , q))
---- reduce-trans-to {n = n₁} (`-stepˡ p , equal) rewrite n+0≡n n₁ = `-stepˡ p
---- reduce-trans-to (`-stepˡ p , K-step q) = {!   !}
---- reduce-trans-to (`-stepˡ p , S-step q) = {!   !}
---- reduce-trans-to (`-stepˡ p , `-stepˡ q) = {!   !}
---- reduce-trans-to (`-stepˡ p , `-stepʳ q) = {!   !}
---- reduce-trans-to (`-stepʳ p , q) = {!   !}

---- reduce-trans-from
----   : ∀ {x y z n m}
----   → x -[ n + m ]→ z → ((x -[ n ]→ y) × (y -[ m ]→ z))
---- reduce-trans-from {n = zero} p = {!   !}
---- reduce-trans-from {n = suc n} p = {!   !}

---- reduce-trans-iso
----   : ∀ {x y z n m}
----   → ((x -[ n ]→ y) × (y -[ m ]→ z)) ≃ x -[ n + m ]→ z
---- reduce-trans-iso = record
----   { to = reduce-trans-to
----   ; from = ?
----   ; from∘to≡id = ?
----   ; to∘from≡id = ?
----   }

--NormalForm : SK → Set
--NormalForm x = ¬ Reducible x
---- equivalent:
---- NormalForm x = ∀ {x' n} → x -[ n ]→ x' → n ≡ zero
---- TODO could try to make an iso out of this just for fun

--normalForm? : ∀ x → Dec (NormalForm x)
--normalForm? x with reducible? x
--... | yes p = no λ z → z p
--... | no ¬p = yes ¬p

--Normalizable : SK → Set
--Normalizable x = ∃[ x' ] ((x -[]→ x') × NormalForm x')

---- halting problem without input:
---- I believe - though don't hold me to this - that you cannot
---- prove this. Instead we'll likely have to prove that it's
---- impossible to construct an SK expression that can determine
---- whether any other SK expression is normalizable.
---- Actually, you really shouldn't be able to prove it, since you
---- can introduce halting oracle's without getting contradictions,
---- and that's effectively what this is. I'm vaguely wondering if
---- the existence of a halting oracle is equivalent to the law of
---- the excluded middle, but I suspect it isn't. (Also there's an
---- infinite hierarchy of halting oracles, keep that in mind.) In
---- light of that I also wonder if we can prove the negative of
---- this (so double negative of halting problem.) Probably not
---- though?
---- Also - it seems a bit odd that this returs a *proof* of
---- halting, since it seems like that should be impossible to
---- obtain, in general - at least a finite proof, that is, and I do
---- believe we can only represent finite proofs here. So, maybe it
---- makes more sense for it to return
---- Dec (¬ (¬ Normalizable x))
---- This makes it impossible to actually obtain the proof, even if
---- we add double negation elimination as an axiom (we can prove
---- the statement, but we can't run it and get the proof out), and
---- instead just asserts that you can't disprove it.
---- But I could be wrong there, maybe this type is fine for an
---- oracle.
---- And then of course we have the post
---- https://www.alignmentforum.org/posts/yjC5LmjSRD2hR9Pfa/on-the-falsifiability-of-hypercomputation
---- which specifically talks about constructive halting oracles,
---- outputting a number of steps after which the given turing
---- machine is guaranteed to have halted
---- ¬normalizable? : ¬ ∀ x → Dec (Normalizable x)
---- ¬normalizable? p = ?

---- interlude: Specialized double negation elimination
--weak-dne : ∀ {x} → ¬ ¬ ¬ x → ¬ x
--weak-dne ¬¬¬p = λ p → ¬¬¬p λ ¬p → ¬p p

---- To be able to say anything really interesting, we will need a
---- Goedel numbering for SK-expressions.
---- Goedelℕ : ℕ → SK → Set
---- TODO

--Cycle : SK → Set
--Cycle x = x -[]→ x

--step : ∀ {x y n} → x -[ suc n ]→ y → ∃[ x' ] (x' -[ n ]→ y)
--step (K-step p) = -, p
--step (S-step p) = -, p
--step (`-stepˡ p) with step p
--... | _ , q = -, `-stepˡ q
--step (`-stepʳ p) with step p
--... | _ , q = -, `-stepʳ q

---- nSteps : (n : ℕ) → x -[ n + m ]→ y → ∃[ x' ] (x' -[ m ]→ y)

---------------------------------------

---- if an expression is reducible at least n times, it is called
---- n-reducible (I made up the term)
---- isNReducible? : (x : SK)
----              → Dec (∃[ n ] ∃[ x' ] (x -[ n ]→ x'))
---- isNReducible? = ?

---- step : ∀ x y {n} → x -[ suc n ]→ y → Σ[ x' ∈ SK ] (x' -[ n ]→ y)
---- step x y p = ?

---- NB: The output type is a bit awkward, being a decidable
---- of a negative property
---- NB: this is obsolete
---- nSteps : ℕ → SK → Σ[ x ∈ SK ] Dec (ℕ × ¬ Reducible x)
---- nSteps zero x with reducible x
---- ... | yes p = x , no λ z → ?
---- ... | no ¬p = {!   !}
---- nSteps (suc n) x = {!   !}

---- step : SK → Maybe SK
---- step (K ` x ` y) = just x
---- step (S ` x ` y ` z) = just $ x ` z ` (y ` z)
---- step (x ` y) = maybe ((x `_) <$> step y) (just ∘ (_` y)) (step x)
---- step _ = nothing

---- nSteps : ℕ → SK → Maybe ℕ × SK
---- nSteps zero x = nothing , x
---- nSteps (suc k) x = maybe (just k , x) (nSteps k) (step x)

---- {-# NON_TERMINATING #-}
---- eval : SK → SK
---- eval x = maybe x eval (step x)

--size : SK → ℕ
--size S = 1
--size K = 1
--size (x ` y) = size x + size y

--data ℕExtractable : (x : SK) → Set where
--  zero : ℕExtractable skZero
--  suc  : ∀ {x} → ℕExtractable x → ℕExtractable (skSuc ` x)

--ℕasSK : ℕ → SK
--ℕasSK zero = skZero
--ℕasSK (suc n) = skSuc ` ℕasSK n

--ℕasSKExtractor : (n : ℕ) → ℕExtractable (ℕasSK n)
--ℕasSKExtractor zero = zero
--ℕasSKExtractor (suc n) = suc (ℕasSKExtractor n)

---- IsFixpoint : SK → Set
---- IsFixpoint x = step x ≡ nothing

---- TODO rewrite in terms of NormalForm
---- ℕasSKfixpoint : (n : ℕ) → IsFixpoint (ℕasSK n)
---- ℕasSKfixpoint zero = refl
---- ℕasSKfixpoint (suc n) rewrite ℕasSKfixpoint n = refl
---- equivalent:
---- ℕasSKfixpoint (suc n) with step (ℕasSK n) | ℕasSKfixpoint n
---- ℕasSKfixpoint (suc n)    | .nothing       | refl = refl

--instance
--  DecInvariant : RawInvariant Dec
--  DecInvariant = record
--    { invmap = λ fʸ fⁿ → foldDec (yes ∘ fʸ) (no ∘ (_∘ fⁿ))
--    }

---- making this an instance breaks things
--FunctorInvariant : {F : Set → Set} → {{RawFunctor F}}
--                 → RawInvariant F
--FunctorInvariant = record
--  { invmap = const ∘ _<$>_
--  }

--ℕExtractable? : (x : SK) → Dec (ℕExtractable x)
--ℕExtractable? skZero = yes zero
--ℕExtractable? (skSuc ` x) =
--  invmap suc (λ where (suc p) → p) (ℕExtractable? x)
--ℕExtractable? S = no λ ()
--ℕExtractable? K = no λ ()
--ℕExtractable? (S ` x) = no λ ()
--ℕExtractable? (K ` S) = no λ ()
--ℕExtractable? (K ` K) = no λ ()
--ℕExtractable? (K ` (S ` x)) = no λ ()
--ℕExtractable? (K ` (K ` x)) = no λ ()
--ℕExtractable? (K ` (S ` S ` x)) = no λ ()
--ℕExtractable? (K ` (S ` K ` S)) = no λ ()
--ℕExtractable? (K ` (S ` K ` (x ` y))) = no λ ()
--ℕExtractable? (K ` (S ` (x ` y) ` z)) = no λ ()
--ℕExtractable? (K ` (K ` x ` y)) = no λ ()
--ℕExtractable? (K ` (x ` y ` z ` w)) = no λ ()
--ℕExtractable? (K ` x ` y) = no λ ()
--ℕExtractable? (S ` S ` x) = no λ ()
--ℕExtractable? (S ` K ` x) = no λ ()
--ℕExtractable? (S ` (S ` x) ` y) = no λ ()
--ℕExtractable? (S ` (K ` x) ` y) = no λ ()
--ℕExtractable? (S ` (S ` S ` y) ` z) = no λ ()
--ℕExtractable? (S ` (S ` K ` y) ` z) = no λ ()
--ℕExtractable? (S ` (S ` (S ` x₁) ` y) ` z) = no λ ()
--ℕExtractable? (S ` (S ` (K ` S) ` S) ` z) = no λ ()
--ℕExtractable? (S ` (S ` (K ` S) ` (y ` y₁)) ` z) = no λ ()
--ℕExtractable? (S ` (S ` (K ` K) ` x) ` y) = no λ ()
--ℕExtractable? (S ` (S ` (K ` (x ` y)) ` z) ` w) = no λ ()
--ℕExtractable? (S ` (S ` (x ` y ` z) ` w) ` u) = no λ ()
--ℕExtractable? (S ` (K ` x ` y) ` z) = no λ ()
--ℕExtractable? (S ` (x ` y ` z ` w) ` v) = no λ ()
--ℕExtractable? (x ` y ` z ` w) = no λ ()

--extractℕ : (x : SK) → ℕExtractable x → ℕ
--extractℕ skZero zero = zero
--extractℕ (skSuc ` x) (suc p) = suc (extractℕ x p)

--ℕ≃ℕSK : ℕ ≃ Σ SK ℕExtractable
--ℕ≃ℕSK = record
--  { to = λ n → ℕasSK n , ℕasSKExtractor n
--  ; from = uncurry extractℕ
--  ; from∘to≡id = ftid
--  ; to∘from≡id = tfid
--  }
--  where
--    ftid : (n : ℕ) → extractℕ (ℕasSK n) (ℕasSKExtractor n) ≡ n
--    ftid zero = refl
--    ftid (suc n) rewrite ftid n = refl
--    tfid : (ℕx : Σ SK ℕExtractable)
--         → let n = uncurry extractℕ ℕx
--           in (ℕasSK (n) , ℕasSKExtractor (n)) ≡ ℕx
--    tfid (_ , zero) = refl
--    tfid ((_ ` x) , suc p) with extractℕ x p | tfid (x , p)
--    ... | _ | refl = refl
