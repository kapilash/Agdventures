{-# OPTIONS --safe --guardedness #-}
module CSP1 where

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


data VMS : Set where
  coin : VMS
  chocolate : VMS


instance
  vms-deceq : HasDecEq VMS
  (vms-deceq HasDecEq.≟ coin) coin = yes refl
  (vms-deceq HasDecEq.≟ coin) chocolate = no λ ()
  (vms-deceq HasDecEq.≟ chocolate) coin = no λ ()
  (vms-deceq HasDecEq.≟ chocolate) chocolate = yes refl

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
  Success : Alphabetⱼ


stepⱼ :  Jugs → Alphabetⱼ -> Jugs
stepⱼ j Success = j
stepⱼ [small= s &big= b ] FillSmall = [small= 3 &big= b ]
stepⱼ [small= s &big= b ] FillBig = [small= s &big= 5 ]
stepⱼ [small= s &big= b ] EmptySmall = [small= 0 &big= b ]
stepⱼ [small= s &big= b ] EmptyBig = [small= s &big= 0 ]
stepⱼ [small= s &big= b ] PourSmallToBig with (s + b) ≤? 5
... | yes _ = [small= 0 &big= (s + b) ]
... | no _ = [small= (s ∸ (5 ∸ b )) &big= 5 ]
stepⱼ [small= s &big= b ] PourBigToSmall with (s + b) ≤? 3
... | yes _ = [small= (s + b) &big= 0 ]
... | no _ = [small= 3 &big= (b ∸  ( 3 ∸ s )) ] 




data Processₐ (Alphabet : Set) : Set where
 STOPₓ : Processₐ Alphabet
 _→ᵢ_ : Alphabet → Processₐ Alphabet → Processₐ Alphabet


_ : Processₐ VMS
_ = coin →ᵢ STOPₓ

_ : Processₐ VMS
_ = coin →ᵢ (chocolate →ᵢ (coin →ᵢ (chocolate →ᵢ STOPₓ)))

record Clock : Set where
  coinductive
  field
    hd : Tick
    tl : Clock

clock₁ : Clock
clock₁ .Clock.hd = tick
clock₁ .Clock.tl = clock₁

Coin : VMS → Set
Coin c = c ≡ coin

Choc : VMS → Set
Choc c = c ≡ chocolate

record VM₂ : Set where
  coinductive
  field
    insert : Σ VMS Coin
    extract : Σ VMS Choc → VM₂

vm₂ : VM₂
vm₂ .VM₂.insert = coin , refl
vm₂ .VM₂.extract (chocolate , snd) = vm₂


record Process₁ (Alphabet : Set) : Set where
  coinductive
  field
    step : Maybe (Σ Alphabet (λ _ → Process₁ Alphabet)) 


clock₂ : Process₁ Tick
clock₂ .Process₁.step = just (tick , clock₂ )

vm : Process₁ VMS
vm .Process₁.step = just (coin , record { step = just (chocolate , vm) })

broken-vm₁ : Process₁ VMS
broken-vm₁ .Process₁.step = just (coin , (record { step = nothing }))


STOPₐ : ∀ {A : Set} → Process₁ A
STOPₐ {A} .Process₁.step = nothing


_→₂_ : ∀ {A : Set} → A → Process₁ A → Process₁ A
(x →₂ p) .Process₁.step = just (x , p)

broken-vm₂ : Process₁ VMS
broken-vm₂ .Process₁.step = just (coin , STOPₐ)

broken-vm₃ : Process₁ VMS
broken-vm₃ = coin →₂ STOPₐ


record Process (Alphabet : Set) : Set where
  coinductive
  field
    step : Alphabet → Maybe (Process Alphabet)

STOP : ∀ {A : Set} → Process A
STOP .Process.step _ = nothing

_→ₚ_ : ∀ {A : Set} → {{ HasDecEq A }} → A → Process A → Process A
_→ₚ_  x p .Process.step y with x ≟ y
... | no ¬a = nothing
... | yes a = just p


broken-vm : Process VMS
broken-vm = coin →ₚ STOP

clock : Process Tick
clock .Process.step _ = just clock


diehard : Process Alphabetⱼ
diehard = diehard-from [small= 0 &big= 0 ]
 where
 diehard-from : Jugs → Process Alphabetⱼ
 diehard-from j .Process.step a with a | is-eq? (j .big) 4
 ... | Success | no ¬a = nothing
 ... | Success | yes a₁ = just STOP
 ... | other | _ = just (diehard-from (stepⱼ  j other))


simple-vms : Process VMS
simple-vms .Process.step chocolate = nothing
simple-vms .Process.step coin = just simple-vms'
  where
  simple-vms' : Process VMS
  simple-vms' .Process.step coin = nothing
  simple-vms' .Process.step chocolate = just simple-vms


choice : ∀ {A : Set} → {{ HasDecEq A }} → (x : A) → Process A → (y : A) → Process A → x ≢ y → Process A
choice x P y Q neq .Process.step a with x ≟ a | y ≟ a
... | yes a₁ |  _ = just P
... | no ¬a  | yes _ = just Q
... | no ¬a₁ | no _ = nothing

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


_ : broken-vm has-trace (coin ∷ [])
_ = trace-step refl trace-empty


_ : broken-vm has-trace []
_ = trace-empty

diehard-lemma : diehard has-trace (FillBig ∷ PourBigToSmall ∷ EmptySmall ∷ PourBigToSmall ∷ FillBig ∷ PourBigToSmall ∷ Success ∷ [])
diehard-lemma = trace-step refl (trace-step refl (trace-step refl (trace-step refl (trace-step refl (trace-step refl (trace-step refl trace-empty)) ))))

diehard-state-from-trace : Trace Alphabetⱼ → Jugs
diehard-state-from-trace t = (foldl stepⱼ [small= 0 &big= 0 ] t)


-- Law 7 from page 30
prefix-closed : ∀ {A} {P : Process A} {s t} → P has-trace (s ++ t) → P has-trace s
prefix-closed {A} {P} {[]} {t} x = trace-empty
prefix-closed {A} {P} {x₁ ∷ s} {t} (trace-step x p') = trace-step x (prefix-closed p')


-- stop has only empty trace
stop-only-empty : ∀ {A} → {s : List A} → (STOP {A}) has-trace s → s ≡ []
stop-only-empty {A} {s} trace-empty = refl

