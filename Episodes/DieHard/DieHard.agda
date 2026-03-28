{-# OPTIONS --safe --guardedness #-}
module DieHard where

open import Data.Nat
open import Data.Nat.Properties
open import Relation.Nullary.Decidable
open import Relation.Binary.PropositionalEquality as Eq
open Eq
open import Data.Product

record Jugs : Set where
  constructor [small=_&big=_]
  field
    small : ℕ
    big : ℕ
open Jugs

emptyJugs : Jugs
emptyJugs = [small= zero &big= zero ]

fullJugs : Jugs
fullJugs = [small= 3 &big= 5 ]

exactlyFour : Jugs → Set
exactlyFour jugs = big jugs ≡ 4


big-capacity : Jugs → Set
big-capacity jugs = big jugs ≤ 5

small-capacity : Jugs → Set
small-capacity jugs = small jugs ≤ 3

capacity≤8 : Jugs → Set
capacity≤8 jugs = small-capacity jugs × big-capacity jugs 


data Action : Set where
  FillSmall : Action
  FillBig : Action
  EmptySmall : Action
  EmptyBig : Action
  PourSmallToBig : Action
  PourBigToSmall : Action

step :  Jugs → Action -> Jugs
step [small= s &big= b ] FillSmall = [small= 3 &big= b ]
step [small= s &big= b ] FillBig = [small= s &big= 5 ]
step [small= s &big= b ] EmptySmall = [small= 0 &big= b ]
step [small= s &big= b ] EmptyBig = [small= s &big= 0 ]
step [small= s &big= b ] PourSmallToBig with (s + b) ≤? 5
... | yes _ = [small= 0 &big= (s + b) ]
... | no _ = [small= (s ∸ (5 ∸ b )) &big= 5 ]
step [small= s &big= b ] PourBigToSmall with (s + b) ≤? 3
... | yes _ = [small= (s + b) &big= 0 ]
... | no _ = [small= 3 &big= (b ∸  ( 3 ∸ s )) ] 

big-capacity-lemma : (jugs : Jugs) → (action : Action) →  big-capacity jugs → big-capacity (step jugs action)
big-capacity-lemma [small= s &big= b ] FillSmall cap = cap
big-capacity-lemma [small= s &big= b ] FillBig cap = s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))
big-capacity-lemma [small= s &big= b ] EmptySmall cap = cap
big-capacity-lemma [small= s &big= b ] EmptyBig cap = z≤n
big-capacity-lemma [small= s &big= b ] PourSmallToBig cap with (s + b) ≤? 5
... | yes x = x
... | no _ = s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))
big-capacity-lemma [small= s &big= b ] PourBigToSmall cap with (s + b) ≤? 3
... | yes x = z≤n
... | no x  = ≤-trans (m∸n≤m b (3 ∸ s)) cap -- transitivity of ≤ via m∸n≤m

small-capacity-lemma : (jugs : Jugs) → (action : Action) → small-capacity jugs → small-capacity (step jugs action)
small-capacity-lemma [small= s &big= b ] FillSmall cap = s≤s (s≤s (s≤s z≤n))
small-capacity-lemma [small= s &big= b ] FillBig cap = cap
small-capacity-lemma [small= s &big= b ] EmptySmall cap = z≤n
small-capacity-lemma [small= s &big= b ] EmptyBig cap = cap
small-capacity-lemma [small= s &big= b ] PourSmallToBig cap with (s + b) ≤? 5
... | yes x = z≤n
... | no _ =  ≤-trans (m∸n≤m s (5 ∸ b)) cap -- transitivity of ≤ via m∸n≤m  
small-capacity-lemma [small= s &big= b ] PourBigToSmall cap with (s + b) ≤? 3
... | yes x =  x
... | no _ =  s≤s (s≤s (s≤s z≤n))

capacity-lemma : (jugs : Jugs) → (action : Action) →  capacity≤8 jugs → capacity≤8 (step jugs action)
capacity-lemma jugs action (cap₁ , cap₂) = (small-capacity-lemma jugs action cap₁ ) , (big-capacity-lemma jugs action cap₂)

record DieHardSM : Set where
  coinductive
  field
    current : Jugs
    next : Action → DieHardSM

open DieHardSM

mkStateMachine : Jugs → DieHardSM
mkStateMachine jugs .current = jugs
mkStateMachine jugs .next action = mkStateMachine (step jugs action)

data ∃F  (P : Jugs → Set) : DieHardSM → Set where
  now : ∀ {stream : DieHardSM} → P (current stream) →  ∃F P stream
  later : ∀ {stream : DieHardSM} → (action : Action) →   ∃F P (next stream action) → ∃F P stream

simon-says : ∃F exactlyFour (mkStateMachine  [small= 0 &big= 0 ])
simon-says = later FillBig 
             (later PourBigToSmall
             (later EmptySmall
             (later PourBigToSmall
             (later FillBig
             (later PourBigToSmall
             (now refl))))))

record ∀G (P : Jugs → Set) (stream : DieHardSM) : Set where
  coinductive
  field
   currently : P (current stream)
   always : ∀ (action : Action) → ∀G P (next stream action)
open ∀G

start-cap⇒∀G-cap : ∀ (jugs : Jugs) → capacity≤8 jugs → ∀G (capacity≤8) (mkStateMachine jugs)
start-cap⇒∀G-cap jugs c .currently = c
start-cap⇒∀G-cap jugs c .always action = start-cap⇒∀G-cap (step jugs action) (capacity-lemma jugs action c) 
