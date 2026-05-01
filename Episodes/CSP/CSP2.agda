{-# OPTIONS --safe --guardedness #-}
module CSP2 where

open import Data.Nat renaming (_≟_ to is-eq? )
open import Relation.Nullary.Decidable
open import Relation.Binary.PropositionalEquality as Eq
open Eq
open import Data.Product
open import Data.Maybe
open import Data.Maybe.Properties
open import Relation.Binary
open import Relation.Nullary.Negation
open import Data.Bool hiding ( _<?_; _≟_; _<_; _≤?_)
open import Data.Bool.Properties hiding ( _<?_; _≟_; _≤?_ )
open import Data.List
open import Data.List.Properties
open import Data.Sum

record HasDecEq (A : Set) : Set where
  field
    _≟_ : DecidableEquality A

open HasDecEq {{...}}

data Tick : Set where
 tick : Tick

instance
   tick-deceq : HasDecEq Tick
   (tick-deceq HasDecEq.≟ tick) tick = yes refl

record Jugs : Set where
  constructor [small=_&big=_]
  field
    small : ℕ
    big : ℕ
open Jugs


data Alphabetⱼ : Set where
  FillSmall : Alphabetⱼ
  FillBig : Alphabetⱼ
  EmptySmall : Alphabetⱼ
  EmptyBig : Alphabetⱼ
  PourSmallToBig : Alphabetⱼ
  PourBigToSmall : Alphabetⱼ

record Process (Alphabet : Set) : Set where
  coinductive
  field
    step : Alphabet → Maybe (Process Alphabet)

STOP : ∀ {A : Set} → Process A
STOP .Process.step _ = nothing

Runₐ : ∀ {A : Set} → Process A
Runₐ .Process.step x = just Runₐ

_→ₚ_ : ∀ {A : Set} → {{ HasDecEq A }} → A → Process A → Process A
_→ₚ_  x p .Process.step y with x ≟ y
... | no ¬a = nothing
... | yes a = just p


clock : Process Tick
clock .Process.step _ = just clock

choice : ∀ {A : Set} → {{ HasDecEq A }} → (x : A) → Process A → (y : A) → Process A → x ≢ y → Process A
choice x P y Q neq .Process.step a with x ≟ a | y ≟ a
... | yes a₁ |  _ = just P
... | no ¬a  | yes _ = just Q
... | no ¬a₁ | no _ = nothing


data MaybeRel {A : Set} (R : A → A → Set) : Maybe A → Maybe A → Set where
  both-nothing : MaybeRel R nothing nothing
  both-just : ∀ { x y } → R x y → MaybeRel R (just x) (just y)

record _∼_ {A : Set}  (P Q : Process A) : Set where
  coinductive
  field
     step-sim : ∀ (a : A) → MaybeRel _∼_ (Process.step P a) (Process.step Q a)


infixl 4 _∼_


∼-refl : {A : Set} → (P : Process A) → (P ∼ P)
∼-refl P ._∼_.step-sim a with P .Process.step a
... | just x = both-just (∼-refl x)
... | nothing = both-nothing

~-cong : {A : Set} → {{ hde : HasDecEq A }} → {P Q : Process A}  →  (x : A) → (P ∼ Q) → (x →ₚ P) ∼ (x →ₚ Q)
~-cong x p~q ._∼_.step-sim a with x ≟ a
... | no ¬a = both-nothing
... | yes a₁ = both-just p~q

~-sym : {A : Set} → {P Q : Process A} → (P ∼ Q) → (Q ∼ P)
~-sym {A} {P} {Q} pq ._∼_.step-sim a  with (P .Process.step a) | (Q .Process.step a) | (pq ._∼_.step-sim a)
... | just p | just q  | both-just p~q = both-just (~-sym p~q)
... | nothing | nothing | _ = both-nothing 

~-trans : {A : Set} → {P Q R : Process A} → (P ∼ Q) → (Q ∼ R) → (P ∼ R)
~-trans {A} {P} {Q} {R} pq qr ._∼_.step-sim a with (P .Process.step a) | (Q .Process.step a) |  (R .Process.step a)
                                   | (pq ._∼_.step-sim a) | (qr ._∼_.step-sim a) 
... | just x₁ | just x₂ | just x₃ | both-just x | both-just x₄ = both-just (~-trans x x₄)
... | nothing | nothing | nothing | both-nothing | both-nothing = both-nothing


choice-comm : ∀ {A} → {{ k : HasDecEq A }} → (x : A) → (P : Process A) → (y : A) → (Q : Process A) → (neq : x ≢ y) → choice x P y Q neq ∼ choice {A} {{k}} y Q x P  (≢-sym neq) 
choice-comm {A} {{k}} x P y Q neq ._∼_.step-sim a with x ≟ a | y ≟ a
... | no ¬a | no ¬a₁ =  both-nothing
... | no ¬a | yes a₁ = both-just (∼-refl Q)
... | yes a₁ | no ¬a = both-just (∼-refl P)
... | yes a₁ | yes a₂ = contradiction-irr (trans a₁ (sym a₂)) neq


Trace : Set → Set
Trace A = List A

data _has-trace_ {A : Set} (P : Process A) : Trace A → Set where
  trace-empty : P has-trace []
  trace-step  : ∀ {a s} {P' : Process A} → 
                (P .Process.step a ≡ just P') → 
                (P' has-trace s) → 
                (P has-trace (a ∷ s))


_ : clock has-trace (tick ∷ tick ∷ [])
_ = trace-step refl (trace-step refl trace-empty)

_ : ∀ {A : Set}  → (STOP {A}) has-trace  []
_ = trace-empty


infixl 4 _⊑_
infix 4 _≈ₜ_
infixl 7 _||_
infixl 7 _↑_||_↑_


_⊑_ : {A : Set} → Process A → Process A → Set
P ⊑ Q = ∀ {t} → P has-trace t → Q has-trace t


⊑-refl : {A : Set} → (P : Process A) → P ⊑ P
⊑-refl {A} P pht = pht

⊑-trans : {A : Set} → {P Q R : Process A} → P ⊑ Q → Q ⊑ R → P ⊑ R
⊑-trans {A} {P} {Q} {R} pq qr {t} rht = qr (pq rht)

⊑-STOP : ∀ {A} → (P : Process A) → STOP ⊑ P
⊑-STOP {A} P {s} trace-empty = trace-empty

⊑-RUN : ∀ {A} → (P : Process A) → P ⊑ Runₐ
⊑-RUN {A} P {s} trace-empty = trace-empty
⊑-RUN {A} P {s} (trace-step x pht) = trace-step refl (⊑-RUN _ pht)


_≈ₜ_ : {A : Set} → Process A → Process A → Set
P ≈ₜ Q = (P ⊑ Q) × (Q ⊑ P)


∼→⊑ : ∀ {A} {P Q : Process A} → (P ∼ Q) → (P ⊑ Q)
∼→⊑ {A} {P} {Q} pq {t} trace-empty = trace-empty
∼→⊑ {A} {P} {Q} pq {t} (trace-step {a} {s} {P'} pa p's) with (P .Process.step a) | (Q .Process.step a) |  (pq ._∼_.step-sim a) | pa | inspect (Q .Process.step) a
... | just _ | (just Q') | both-just p'~q' | refl | [ qa ] = trace-step qa (∼→⊑ p'~q' p's)

∼→≈ₜ : ∀ {A}  {P Q : Process A} → P ∼ Q → P ≈ₜ Q
∼→≈ₜ {A} {P} {Q} pq = (∼→⊑ pq) , (∼→⊑ (~-sym pq) )


_||_ : ∀ {A : Set} → Process A → Process A → Process A
(P || Q) .Process.step x with P .Process.step x | Q .Process.step x
... | just p | just q   =  just ( p || q)
... | just p | nothing  =  nothing
... | nothing | just q  =  nothing
... | nothing | nothing =  nothing


||-comm : ∀ {A} → (P Q : Process A) → P || Q ∼ Q || P
||-comm P Q ._∼_.step-sim a with P .Process.step a | Q .Process.step a
... | just p | just q = both-just (||-comm p q) 
... | just x | nothing = both-nothing
... | nothing | just q = both-nothing
... | nothing | nothing = both-nothing


||-assoc : ∀ {A} → (P Q R : Process A) → (P || Q) || R ∼ P || (Q || R)
||-assoc P Q R ._∼_.step-sim a with P .Process.step a | Q .Process.step a | R .Process.step a
... | just p | just q | just r = both-just (||-assoc p q r)
... | just p | just q | nothing = both-nothing
... | just p | nothing | just r = both-nothing
... | just p | nothing | nothing = both-nothing
... | nothing | just q | just r = both-nothing
... | nothing | nothing | just r = both-nothing
... | nothing | just q | nothing = both-nothing
... | nothing | nothing | nothing = both-nothing

||-stop : ∀ {A} → (P : Process A) → (P || STOP) ∼ STOP
||-stop p ._∼_.step-sim a with p .Process.step a
... | just x = both-nothing
... | nothing = both-nothing

||-run : ∀ {A} → (P : Process A) → (P || Runₐ) ∼ P
||-run p ._∼_.step-sim a with p .Process.step a
... | just x = both-just ( ||-run  x)
... | nothing = both-nothing

_↑_||_↑_ : ∀ {A : Set} → Process A →  (A → Bool) → Process A → (A → Bool) → Process A
_↑_||_↑_ {A} p₁ is-member₁ p₂ is-member₂ .Process.step x with (is-member₁ x) | (is-member₂ x) | (p₁ .Process.step x) | (p₂ .Process.step x)
... | false | false | maybe₁ | maybe₂ = nothing
... | false | true | _ | just p₂' = just (p₁ ↑ is-member₁ || p₂' ↑ is-member₂)
... | false | true | _ | nothing = nothing
... | true | false | just p₁' | _ = just (p₁' ↑ is-member₁ || p₂ ↑ is-member₂)
... | true | false | nothing | _ = nothing
... | true | true | just p₁' | just p₂' = just (p₁' ↑ is-member₁ || p₂' ↑ is-member₂)
... | _    | _    | _        | _        = nothing



mα? : Alphabetⱼ → Bool
mα? FillSmall = false
mα? FillBig = true
mα? EmptySmall = false
mα? EmptyBig = true
mα? PourSmallToBig = true
mα? PourBigToSmall = true


zα? : Alphabetⱼ → Bool
zα? FillSmall = true
zα? FillBig = false
zα? EmptySmall = true
zα? EmptyBig = false
zα? PourSmallToBig = true
zα? PourBigToSmall = true

mclane : Process Alphabetⱼ
mclane .Process.step x = just mclane



zeus : Process Alphabetⱼ
zeus .Process.step x = just zeus

-- Same problem as DieHard.agda and Chapter1, now decomposed via CSP parallel composition
diehard₃ : Process Alphabetⱼ
diehard₃ = mclane ↑ mα? || zeus ↑ zα?

diehard-lemma : diehard₃ has-trace (FillBig ∷ PourBigToSmall ∷ EmptySmall ∷ PourBigToSmall ∷ FillBig ∷ PourBigToSmall ∷  [])
diehard-lemma = trace-step refl (trace-step refl (trace-step refl (trace-step refl (trace-step refl (trace-step refl trace-empty)))))

