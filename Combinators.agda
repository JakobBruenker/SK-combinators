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

foldℕ : {r : Set} → r → (r → r) → (n : ℕ) → r
foldℕ z _ zero = z
foldℕ z s (suc n) = s (foldℕ z s n)

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

infix 1 _-[_]→_

-- x can be reduced to y in exactly n steps
data _-[_]→_ : (x : SK) → (steps : ℕ) → (y : SK) → Set where
  equal : ∀ {x} → x -[ zero ]→ x
  K-step : ∀ {x y z n} → x -[ n ]→ z
         → K ` x ` y -[ suc n ]→ z
  S-step : ∀ {x y z w n} → x ` z ` (y ` z) -[ n ]→ w
         → S ` x ` y ` z -[ suc n ]→ w
  `-stepˡ : ∀ {x x' y n} → x -[ n ]→ x' → x ` y -[ n ]→ x' ` y
  `-stepʳ : ∀ {x y y' n} → y -[ n ]→ y' → x ` y -[ n ]→ x ` y'

Reducible : SK → Set
Reducible x = ∃[ x' ] (x -[ 1 ]→ x')

isReducible : (x : SK) → Dec (∃[ x' ] (x -[ 1 ]→ x'))
isReducible S = no λ ()
isReducible K = no λ ()
isReducible (S ` x) with isReducible x
... | yes (x' , p) = yes ((S ` x') , `-stepʳ p)
... | no ¬p = no λ where (_ , `-stepʳ {y' = y'} p) → ¬p (y' , p)
isReducible (K ` x) with isReducible x
... | yes (x' , p) = yes ((K ` x') , `-stepʳ p)
... | no ¬p = no λ where (_ , `-stepʳ {y' = y'} p) → ¬p (y' , p)
isReducible (S ` x ` y) with isReducible x
... | yes (x' , p) = yes ((S ` x' ` y) , `-stepˡ (`-stepʳ p))
... | no ¬p with isReducible y
...   | yes (y' , q) = yes ((S ` x ` y') , `-stepʳ q)
...   | no ¬q = no λ where
  (.(S ` _ ` y) , `-stepˡ (`-stepʳ {y' = y'} p)) → ¬p (y' , p)
  (.(S ` x ` _) , `-stepʳ {y' = y'} p) → ¬q (y' , p)
isReducible (K ` x ` y) = yes (x , K-step equal)
isReducible (S ` y ` z ` w) =
  yes ((y ` w ` (z ` w)) , S-step equal)
isReducible (K ` x ` y ` z) =
  yes ((x ` z) , `-stepˡ (K-step equal))
isReducible (x ` y ` z ` w ` u) with isReducible (x ` y ` z ` w)
... | yes (xyzw' , p) = yes ((xyzw' ` u) , `-stepˡ p)
... | no ¬p with isReducible u
...   | yes (u' , q) = yes ((x ` y ` z ` w ` u') , `-stepʳ q)
...   | no ¬q = no λ where
  (.(_ ` u) , `-stepˡ {x' = x'} p) → ¬p (x' , p)
  (.(x ` y ` z ` w ` _) , `-stepʳ {y' = y'} p) → ¬q (y' , p)

-- TODO (∃[ n ] ∃[ z ] (x -[ suc n ]→ z)) ≃ (∃[ y ] (x -[ 1 ]→ y))

NormalForm : SK → Set
NormalForm x = ¬ Reducible x
-- equivalent:
-- NormalForm x = ∀ {x' n} → x -[ n ]→ x' → n ≡ zero
-- TODO could try to make an iso out of this just for fun

-- TODO isNormalForm :i ∀ x → Dec (NormalForm x)

infix 1 _-[]→_

_-[]→_ : SK → SK → Set
x -[]→ y = ∃[ n ] (x -[ n ]→ y)

Cycle : SK → Set
Cycle x = x -[]→ x

-- lemma : ∀ {x y n} → S ` x -[ n ]→ y → ∃[ y' ] (x -[ n ]→ y')
-- lemma equal = -, equal
-- lemma {n = zero} (`-stepˡ x) = -, equal
-- lemma (`-stepʳ x) = -, x

step : ∀ {x y n} → x -[ suc n ]→ y → ∃[ x' ] (x' -[ n ]→ y)
step (K-step p) = -, p
step (S-step p) = -, p
step (`-stepˡ p) with step p
... | _ , q = -, `-stepˡ q
step (`-stepʳ p) with step p
... | _ , q = -, `-stepʳ q

-- nSteps : (n : ℕ) → x -[ n + m ]→ y → ∃[ x' ] (x' -[ m ]→ y)

-- lemma''' : ∀ {x n} → (∀ x' → ¬ (x -[ n ]→ x')) → ∀ {x'}
--       → ¬ (S ` x -[ n ]→ x')
-- lemma''' {x} ¬p (equal p) = ¬p x (equal refl)
-- lemma''' ¬p (`-stepˡ (equal refl) q₁) = lemma''' ¬p q₁
-- lemma''' ¬p (`-stepʳ {y' = y'} q q₁) = ?

-------------------------------------

-- if an expression is reducible at least n times, it is called
-- n-reducible (I made up the term)
-- isNReducible : (x : SK)
--              → Dec (∃[ n ] ∃[ x' ] (x -[ n ]→ x'))
-- isNReducible = ?

-- step : ∀ x y {n} → x -[ suc n ]→ y → Σ[ x' ∈ SK ] (x' -[ n ]→ y)
-- step x y p = ?

-- NB: The output type is a bit awkward, being a decidable
-- of a negative property
-- NB: this is obsolete
-- nSteps : ℕ → SK → Σ[ x ∈ SK ] Dec (ℕ × ¬ Reducible x)
-- nSteps zero x with isReducible x
-- ... | yes p = x , no λ z → ?
-- ... | no ¬p = {!   !}
-- nSteps (suc n) x = {!   !}

-- step : SK → Maybe SK
-- step (K ` x ` y) = just x
-- step (S ` x ` y ` z) = just $ x ` z ` (y ` z)
-- step (x ` y) = maybe ((x `_) <$> step y) (just ∘ (_` y)) (step x)
-- step _ = nothing

-- nSteps : ℕ → SK → Maybe ℕ × SK
-- nSteps zero x = nothing , x
-- nSteps (suc k) x = maybe (just k , x) (nSteps k) (step x)

-- {-# NON_TERMINATING #-}
-- eval : SK → SK
-- eval x = maybe x eval (step x)

size : SK → ℕ
size S = 1
size K = 1
size (x ` y) = size x + size y

data ℕExtractable : (x : SK) → Set where
  zero : ℕExtractable skZero
  suc  : ∀ {x} → ℕExtractable x → ℕExtractable (skSuc ` x)

ℕasSK : ℕ → SK
ℕasSK zero = skZero
ℕasSK (suc n) = skSuc ` ℕasSK n

ℕasSKExtractor : (n : ℕ) → ℕExtractable (ℕasSK n)
ℕasSKExtractor zero = zero
ℕasSKExtractor (suc n) = suc (ℕasSKExtractor n)

-- IsFixpoint : SK → Set
-- IsFixpoint x = step x ≡ nothing

-- ℕasSKfixpoint : (n : ℕ) → IsFixpoint (ℕasSK n)
-- ℕasSKfixpoint zero = refl
-- ℕasSKfixpoint (suc n) rewrite ℕasSKfixpoint n = refl
-- equivalent:
-- ℕasSKfixpoint (suc n) with step (ℕasSK n) | ℕasSKfixpoint n
-- ℕasSKfixpoint (suc n)    | .nothing       | refl = refl

instance
  DecInvariant : RawInvariant Dec
  DecInvariant = record
    { invmap = λ fʸ fⁿ → foldDec (yes ∘ fʸ) (no ∘ (_∘ fⁿ))
    }

-- making this an instance breaks things
FunctorInvariant : {F : Set → Set} → {{RawFunctor F}}
                 → RawInvariant F
FunctorInvariant = record
  { invmap = const ∘ _<$>_
  }

isℕExtractable : (x : SK) → Dec (ℕExtractable x)
isℕExtractable skZero = yes zero
isℕExtractable (skSuc ` x) =
  invmap suc (λ where (suc p) → p) (isℕExtractable x)
isℕExtractable S = no λ ()
isℕExtractable K = no λ ()
isℕExtractable (S ` x) = no λ ()
isℕExtractable (K ` S) = no λ ()
isℕExtractable (K ` K) = no λ ()
isℕExtractable (K ` (S ` x)) = no λ ()
isℕExtractable (K ` (K ` x)) = no λ ()
isℕExtractable (K ` (S ` S ` x)) = no λ ()
isℕExtractable (K ` (S ` K ` S)) = no λ ()
isℕExtractable (K ` (S ` K ` (x ` y))) = no λ ()
isℕExtractable (K ` (S ` (x ` y) ` z)) = no λ ()
isℕExtractable (K ` (K ` x ` y)) = no λ ()
isℕExtractable (K ` (x ` y ` z ` w)) = no λ ()
isℕExtractable (K ` x ` y) = no λ ()
isℕExtractable (S ` S ` x) = no λ ()
isℕExtractable (S ` K ` x) = no λ ()
isℕExtractable (S ` (S ` x) ` y) = no λ ()
isℕExtractable (S ` (K ` x) ` y) = no λ ()
isℕExtractable (S ` (S ` S ` y) ` z) = no λ ()
isℕExtractable (S ` (S ` K ` y) ` z) = no λ ()
isℕExtractable (S ` (S ` (S ` x₁) ` y) ` z) = no λ ()
isℕExtractable (S ` (S ` (K ` S) ` S) ` z) = no λ ()
isℕExtractable (S ` (S ` (K ` S) ` (y ` y₁)) ` z) = no λ ()
isℕExtractable (S ` (S ` (K ` K) ` x) ` y) = no λ ()
isℕExtractable (S ` (S ` (K ` (x ` y)) ` z) ` w) = no λ ()
isℕExtractable (S ` (S ` (x ` y ` z) ` w) ` u) = no λ ()
isℕExtractable (S ` (K ` x ` y) ` z) = no λ ()
isℕExtractable (S ` (x ` y ` z ` w) ` v) = no λ ()
isℕExtractable (x ` y ` z ` w) = no λ ()

extractℕ : (x : SK) → ℕExtractable x → ℕ
extractℕ skZero zero = zero
extractℕ (skSuc ` x) (suc p) = suc (extractℕ x p)

infix 0 _≃_
record _≃_ (A B : Set) : Set where
  field
    to         : A → B
    from       : B → A
    from∘to≡id : ∀ x → from (to x) ≡ x
    to∘from≡id : ∀ y → to (from y) ≡ y

open _≃_  {{...}}

ℕ≃ℕSK : ℕ ≃ Σ SK ℕExtractable
ℕ≃ℕSK = record
  { to = λ n → ℕasSK n , ℕasSKExtractor n
  ; from = uncurry extractℕ
  ; from∘to≡id = ftid
  ; to∘from≡id = tfid
  }
  where
    ftid : (n : ℕ) → extractℕ (ℕasSK n) (ℕasSKExtractor n) ≡ n
    ftid zero = refl
    ftid (suc n) rewrite ftid n = refl
    tfid : (ℕx : Σ SK ℕExtractable)
         → let n = uncurry extractℕ ℕx
           in (ℕasSK (n) , ℕasSKExtractor (n)) ≡ ℕx
    tfid (_ , zero) = refl
    tfid ((_ ` x) , suc p) with extractℕ x p | tfid (x , p)
    ... | _ | refl = refl
