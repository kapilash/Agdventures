{-# OPTIONS  --safe  #-}
module AlphaBeta where

open import Data.Integer renaming ( _⊔_ to _⊔ᵢ_ ; _⊓_ to _⊓ᵢ_ ; _<_ to _<ᵢ_ )
open import Data.Integer.Properties renaming (_<?_  to _<ᵢ?_)
open import Data.List
open import Data.List.Properties using (++-isMonoid ; foldl-++ ; foldl-map ; foldl-cong)
open import Relation.Nullary

open import Data.Nat renaming (_⊔_ to _⊔ₙ_ ; _⊓_ to _⊓ₙ_ )


open import Data.Empty
-- open import Data.Maybe
open import Data.Sum hiding (map)
open import Data.Product hiding (map)
open import Relation.Nullary.Negation
open import Relation.Nullary.Decidable hiding (map)
import Relation.Binary.PropositionalEquality as Eq
open Eq
open Eq.≡-Reasoning
open import Agda.Builtin.Unit

open import Data.Empty using (⊥)
open import Data.Unit.Base using (⊤)
open import Relation.Binary 
open import Data.Bool hiding ( _≟_ )
open import Level renaming (_⊔_ to _⊔ˡ_)
open import Data.List.Relation.Unary.All.Properties using (++↔) 
open import Function.Bundles using (_↔_ )
open import Function
open import Algebra
open import Relation.Binary using (IsEquivalence)
open import Algebra.Properties.Monoid
open import Data.List.NonEmpty renaming (map to map⁺ ; foldl to foldl⁺ ; foldr to foldr⁺ ; concat to concat⁺ )
open import Algebra.Lattice
open import BDL


foldl-accumulator : ∀ {A : Set} {f : Op₂ A} {ϵ : A} → (IsMonoid {A = A} _≡_ f ϵ) → (a : A) → (xs : List A) → foldl f a xs ≡ f a (foldl f ϵ xs)
foldl-accumulator {A} {f} {ϵ} ismonoid a [] = sym (proj₂ (IsMonoid.identity ismonoid) a)
foldl-accumulator {A} {f} {ϵ} ismonoid a (y ∷ xs) = begin
  foldl f (f a y) xs                              ≡⟨ foldl-accumulator ismonoid (f a y) xs ⟩
  f (f a y) (foldl f ϵ xs)                        ≡⟨ IsSemigroup.assoc (IsMonoid.isSemigroup ismonoid) a y (foldl f ϵ xs) ⟩
  f a (f y (foldl f ϵ xs))                        ≡⟨ cong (f a) (sym (foldl-accumulator ismonoid y xs)) ⟩
  f a (foldl f y xs)                              ≡⟨ cong (λ k → f a (foldl f k xs)) (sym (proj₁ (IsMonoid.identity ismonoid) y)) ⟩
  f a (foldl f (f ϵ y) xs)                        ≡⟨⟩
  f a (foldl f ϵ (y ∷ xs))                        ∎

{- for finite lists, if the operator is a monoid, then foldl and foldr are the same.-}
first-duality : ∀ {A : Set} {f : Op₂ A} {ϵ : A} → (IsMonoid {A = A} _≡_ f ϵ) → (xs : List A) →   (foldl f ϵ xs) ≡ (foldr f ϵ xs)
first-duality {A} {f} {ϵ} ismonoid [] = refl
first-duality {A} {f} {ϵ} ismonoid (x ∷ xs)       = begin
   foldl f ϵ (x ∷ xs)                             ≡⟨⟩
   foldl f (f ϵ x) xs                             ≡⟨ cong (λ k → foldl f k xs) (proj₁ (IsMonoid.identity ismonoid) x) ⟩
   foldl f x xs                                   ≡⟨ foldl-accumulator ismonoid x xs ⟩
   f x (foldl f ϵ xs)                              ≡⟨ cong (λ k → f x k)  (first-duality ismonoid xs) ⟩
   f x (foldr f ϵ xs)                              ∎

concat-spec-foldl : ∀ {A : Set} (xss : List (List A)) → concat xss ≡ foldl _++_ [] xss
concat-spec-foldl {A} xss rewrite (first-duality ++-isMonoid xss)  = refl

{-
If the operator is monoid and the seed is the identity of it, to apply it on a list of lists, we get the same result if first concatenate the lists and apply the operator or if we first apply the operator on each list and then apply it on the resulting list.
-}
fold-promotion : ∀ {A : Set} {f : Op₂ A} {ϵ : A} → (IsMonoid {A = A} _≡_ f ϵ) → (xss : List (List A))  → foldl f ϵ (concat xss) ≡ foldl f ϵ (map (foldl f ϵ) xss)
fold-promotion {A} {f} {ϵ} ismonoid [] = refl
fold-promotion {A} {f} {ϵ} ismonoid (xs ∷ xss)                                                   = begin
    foldl f ϵ (concat (xs ∷ xss))                                                                 ≡⟨⟩
    foldl f ϵ (xs ++ (concat xss))                                                                ≡⟨ foldl-++ f ϵ xs (concat xss) ⟩
    foldl f (foldl f ϵ xs) (concat xss)                                                           ≡⟨ foldl-accumulator ismonoid (foldl f ϵ xs ) (concat xss) ⟩
    f (foldl f ϵ xs) (foldl f ϵ (concat xss))                                                     ≡⟨ cong (λ k → f (foldl f ϵ xs) k)  (fold-promotion ismonoid xss) ⟩
    f (foldl f ϵ xs) (foldl f ϵ (map (foldl f ϵ) xss))                                            ≡⟨ sym  (foldl-accumulator ismonoid (foldl f ϵ xs) ((map (foldl f ϵ) xss))) ⟩
    foldl f (foldl f ϵ xs) (map (foldl f ϵ) xss)                                                  ≡⟨ cong  (λ k → foldl f k (map (foldl f ϵ) xss)) (sym (proj₁ (IsMonoid.identity ismonoid) (foldl f ϵ xs))) ⟩
    foldl f (f ϵ (foldl f ϵ xs)) (map (foldl f ϵ) xss)                                            ∎


data Extendedℤ : Set where
  -∞ : Extendedℤ
  Fin : ℤ → Extendedℤ
  +∞ : Extendedℤ


infixl 7 _↓_
infixl 6 _↑_

_↑_ : Extendedℤ → Extendedℤ → Extendedℤ
-∞ ↑ y = y
Fin x ↑ -∞ = Fin x
Fin x ↑ Fin y = Fin ( x ⊔ᵢ y)
Fin x ↑ +∞ = +∞
+∞ ↑ y = +∞

_↓_ : Extendedℤ → Extendedℤ → Extendedℤ
-∞ ↓ y = -∞
Fin x ↓ -∞ = -∞
Fin x ↓ Fin y = Fin (x ⊓ᵢ y ) 
Fin x ↓ +∞ = Fin x
+∞ ↓ y = y

↑-assoc : ∀ (x y z : Extendedℤ) →  (x ↑ y) ↑ z ≡ x ↑ (y ↑ z)
↑-assoc -∞ y z = refl
↑-assoc +∞ y z = refl
↑-assoc (Fin x) -∞ z = refl
↑-assoc (Fin x) +∞ z = refl
↑-assoc (Fin x) (Fin y) -∞ = refl
↑-assoc (Fin x) (Fin y) +∞ = refl
↑-assoc (Fin x) (Fin y) (Fin z) rewrite ⊔-assoc x y z = refl




↓-assoc : ∀ (x y z : Extendedℤ) → (x ↓ y) ↓ z ≡ x ↓ (y ↓ z)
↓-assoc -∞ y z = refl
↓-assoc +∞ y z = refl
↓-assoc (Fin x) -∞ z = refl
↓-assoc (Fin x) +∞ z = refl
↓-assoc (Fin x) (Fin y) -∞ = refl
↓-assoc (Fin x) (Fin y) +∞ = refl
↓-assoc (Fin x) (Fin y) (Fin z) rewrite ⊓-assoc x y z = refl


↑-cong : ∀ {x₁ x₂ y₁ y₂ : Extendedℤ} → x₁ ≡ x₂ → y₁ ≡ y₂ → (x₁ ↑ y₁) ≡ (x₂ ↑ y₂)
↑-cong {x₁} {x₂} {y₁} x₁≡x₂ y₁≡y₂ rewrite x₁≡x₂ | y₁≡y₂ = refl


↓-cong : ∀ {x₁ x₂ y₁ y₂ : Extendedℤ} → x₁ ≡ x₂ → y₁ ≡ y₂ → (x₁ ↓ y₁) ≡ (x₂ ↓ y₂)
↓-cong {x₁} {x₂} {y₁} {y₂} x₁≡x₂ y₁≡y₂ rewrite x₁≡x₂ | y₁≡y₂ = refl

↑-identityʳ : ∀ (x : Extendedℤ) → x ↑ -∞ ≡ x
↑-identityʳ -∞ = refl
↑-identityʳ (Fin x) = refl
↑-identityʳ +∞ = refl

↑-identityˡ : ∀ (x : Extendedℤ) → -∞ ↑ x ≡ x
↑-identityˡ x = refl

↓-identityʳ : ∀ (x : Extendedℤ) → x ↓ +∞ ≡ x
↓-identityʳ -∞ = refl
↓-identityʳ (Fin x) = refl
↓-identityʳ +∞ = refl

↓-identityˡ : ∀ (x : Extendedℤ) → +∞ ↓ x ≡ x
↓-identityˡ x = refl

↓-comm : ∀ (x y : Extendedℤ) → x ↓ y ≡ y ↓ x
↓-comm -∞ -∞ = refl
↓-comm -∞ (Fin x) = refl
↓-comm -∞ +∞ = refl
↓-comm (Fin x) -∞ = refl
↓-comm (Fin x) (Fin y) rewrite ⊓-comm x y = refl
↓-comm (Fin x) +∞ = refl
↓-comm +∞ -∞ = refl
↓-comm +∞ (Fin y) = refl
↓-comm +∞ +∞ = refl

↑-comm : ∀ (x y : Extendedℤ) → x ↑ y ≡ y ↑ x
↑-comm -∞ -∞ = refl
↑-comm -∞ (Fin x) = refl
↑-comm -∞ +∞ = refl
↑-comm +∞ -∞ = refl
↑-comm +∞ (Fin x) = refl
↑-comm +∞ +∞ = refl
↑-comm (Fin x) -∞ = refl
↑-comm (Fin x) (Fin y) rewrite ⊔-comm x y = refl
↑-comm (Fin x) +∞ = refl


↑-isMagma : IsMagma {A = Extendedℤ} _≡_ _↑_
↑-isMagma = record { isEquivalence = Eq.isEquivalence ; ∙-cong = cong₂ _↑_  }

↑-isSemigroup : IsSemigroup {A = Extendedℤ} _≡_ _↑_
↑-isSemigroup = record {
   isMagma = ↑-isMagma ;
   assoc = ↑-assoc   }

↑-isMonoid : IsMonoid {A = Extendedℤ} _≡_ _↑_ -∞
↑-isMonoid = record 
  { isSemigroup = ↑-isSemigroup ;
  identity = (λ x → ↑-identityˡ x) , (λ x → ↑-identityʳ x) }


↓-isMagma : IsMagma {A = Extendedℤ} _≡_ _↓_
↓-isMagma = record { isEquivalence = Eq.isEquivalence ; ∙-cong = cong₂ _↓_  }

↓-isSemigroup : IsSemigroup {A = Extendedℤ} _≡_ _↓_
↓-isSemigroup = record {
   isMagma = ↓-isMagma ;
   assoc = ↓-assoc   }

↓-isMonoid : IsMonoid {A = Extendedℤ} _≡_ _↓_ +∞
↓-isMonoid = record 
  { isSemigroup = ↓-isSemigroup ;
  identity = (λ x → ↓-identityˡ x) , (λ x → ↓-identityʳ x) }

min : List Extendedℤ → Extendedℤ
min = foldl _↓_ +∞

max : List Extendedℤ → Extendedℤ
max = foldl _↑_ -∞

↑-absorbs-↓ : ∀ (x y : Extendedℤ) → x ↑ (x ↓ y) ≡ x
↑-absorbs-↓ -∞ y = refl
↑-absorbs-↓ +∞ y = refl
↑-absorbs-↓ (Fin x) -∞ = refl
↑-absorbs-↓ (Fin x) +∞ rewrite ⊔-idem x =  refl
↑-absorbs-↓ (Fin x) (Fin y) rewrite ⊔-absorbs-⊓ x y = refl

↓-absorbs-↑ : ∀ (x y : Extendedℤ) → x ↓ (x ↑ y) ≡ x
↓-absorbs-↑ -∞ y = refl
↓-absorbs-↑ +∞ y = refl
↓-absorbs-↑ (Fin x) -∞ rewrite ⊓-idem x = refl
↓-absorbs-↑ (Fin x) +∞ = refl
↓-absorbs-↑ (Fin x) (Fin y) rewrite ⊓-absorbs-⊔ x y  = refl


minmax-spec : ∀ (xss : List (List Extendedℤ)) → Extendedℤ
minmax-spec xss = min (map max xss)


↓-distribˡ-↑ : ∀ (x y z : Extendedℤ) → x ↓ (y ↑ z) ≡ (x ↓ y) ↑ (x ↓ z)
↓-distribˡ-↑ -∞ y z = refl
↓-distribˡ-↑ +∞ y z = refl
↓-distribˡ-↑ (Fin x) -∞ z = refl
↓-distribˡ-↑ (Fin x) (Fin y) -∞ = refl
↓-distribˡ-↑ (Fin x) +∞ z rewrite ↑-absorbs-↓ (Fin x) z = refl
↓-distribˡ-↑ (Fin x) (Fin y) +∞ rewrite ⊔-comm (x ⊓ᵢ y) x | ⊔-absorbs-⊓ x y  = refl
↓-distribˡ-↑ (Fin x) (Fin y) (Fin z) rewrite ⊓-distribˡ-⊔ x y z = refl

↓-distribʳ-↑ : ∀ (x y z : Extendedℤ) → (y ↑ z) ↓ x ≡ (y ↓ x) ↑ (z ↓ x)
↓-distribʳ-↑ x y z =  begin
   (y ↑ z) ↓ x                             ≡⟨ ↓-comm (y ↑ z) x ⟩
    x ↓ (y ↑ z)                             ≡⟨ ↓-distribˡ-↑ x y z ⟩
    (x ↓ y) ↑ (x ↓ z)                       ≡⟨ cong (_↑ (x ↓ z)) (↓-comm x y) ⟩
    (y ↓ x) ↑ (x ↓ z)                       ≡⟨ cong ((y ↓ x) ↑_ ) (↓-comm x z) ⟩                 
    (y ↓ x) ↑ (z ↓ x)                       ∎


↑-distribˡ-↓ : ∀ (x y z : Extendedℤ) → x ↑ (y ↓ z) ≡ (x ↑ y) ↓ (x ↑ z)
↑-distribˡ-↓ -∞ y z = refl
↑-distribˡ-↓ +∞ y z = refl
↑-distribˡ-↓ (Fin x) -∞ z rewrite ↓-absorbs-↑ (Fin x) z  = refl
↑-distribˡ-↓ (Fin x) +∞ z = refl
↑-distribˡ-↓ (Fin x) (Fin y) -∞ rewrite ⊓-comm (x ⊔ᵢ y) x | ⊓-absorbs-⊔ x y = refl
↑-distribˡ-↓ (Fin x) (Fin y) +∞ = refl
↑-distribˡ-↓ (Fin x) (Fin y) (Fin z) rewrite ⊔-distribˡ-⊓ x y z = refl

↑-distribʳ-↓ : ∀ (x y z : Extendedℤ) → (y ↓ z) ↑ x ≡ (y ↑ x) ↓ (z ↑ x)
↑-distribʳ-↓ x y z = begin
    (y ↓ z) ↑ x                             ≡⟨ ↑-comm (y ↓ z) x ⟩
    x ↑ (y ↓ z)                             ≡⟨ ↑-distribˡ-↓ x y z ⟩
    (x ↑ y) ↓ (x ↑ z)                       ≡⟨ cong (_↓ (x ↑ z)) (↑-comm x y) ⟩
    (y ↑ x) ↓ (x ↑ z)                       ≡⟨ cong ((y ↑ x) ↓_ ) (↑-comm x z) ⟩                 
    (y ↑ x) ↓ (z ↑ x)                       ∎


_⊙_ :  Extendedℤ →  List Extendedℤ → Extendedℤ
x ⊙ xs = x ↓ (max xs)

max-head : ∀ (x : Extendedℤ) →  (xs : List Extendedℤ) → max (x ∷ xs) ≡ x ↑ (max xs)
max-head x xs                        =  begin
  max (x ∷ xs)                       ≡⟨⟩
  foldl _↑_ -∞ (x ∷ xs)              ≡⟨ foldl-accumulator ↑-isMonoid x xs ⟩
  x ↑ (foldl _↑_ -∞ xs)              ≡⟨⟩
  x ↑ (max xs)                       ∎

↓-over-max : ∀ (x : Extendedℤ) (xs : List Extendedℤ) → x ⊙ xs ≡ max (map (x ↓_) xs)
↓-over-max x [] rewrite ↓-comm x -∞ = refl
↓-over-max x (x₁ ∷ xs)                       = begin
   x ⊙ (x₁ ∷ xs)                             ≡⟨⟩
   x ↓ (max (x₁ ∷ xs))                       ≡⟨ cong (λ k → x ↓ k) (max-head x₁ xs) ⟩
   x ↓ (x₁ ↑ (max xs))                       ≡⟨ ↓-distribˡ-↑ x x₁ (max xs) ⟩
   (x ↓ x₁) ↑ (x ↓ (max xs))                 ≡⟨ cong (λ k → (x ↓ x₁) ↑ k) (↓-over-max x xs) ⟩
   (x ↓ x₁) ↑ (max (map (x ↓_) xs))          ≡⟨ sym (max-head (x ↓ x₁) ((map (x ↓_) xs))) ⟩
   max (x ↓ x₁ ∷ map (x ↓_) xs)              ∎


↑-↓-x : Extendedℤ → Extendedℤ → Extendedℤ → Extendedℤ
↑-↓-x x u v = u ↑ (x ↓ v)

↑-↓-is-lattice : IsLattice  _≡_ _↑_ _↓_
↑-↓-is-lattice = record
                  { isEquivalence = Eq.isEquivalence
                  ; ∨-comm = ↑-comm
                  ; ∨-assoc = ↑-assoc
                  ; ∨-cong = ↑-cong
                  ; ∧-comm = ↓-comm
                  ; ∧-assoc = ↓-assoc
                  ; ∧-cong = ↓-cong
                  ; absorptive = ↑-absorbs-↓ , ↓-absorbs-↑
                  }

↑-↓-isDistributiveLattice : IsDistributiveLattice _≡_ _↑_ _↓_
↑-↓-isDistributiveLattice = record
        { isLattice = ↑-↓-is-lattice
        ; ∨-distrib-∧ = ↑-distribˡ-↓ , ↑-distribʳ-↓
        ; ∧-distrib-∨ = ↓-distribˡ-↑ , ↓-distribʳ-↑ }


↑-↓-isBoundedDistributiveLattice : IsBoundedDistributiveLattice _≡_ _↑_ _↓_ +∞ -∞
↑-↓-isBoundedDistributiveLattice = record
        { isDistributiveLattice = ↑-↓-isDistributiveLattice
        ; ∨-identity = (λ x → ↑-identityˡ x) , (λ x → ↑-identityʳ x)
        ; ∧-identity = (λ x → ↓-identityˡ x) , (λ x → ↓-identityʳ x) }

minmax-lemma-1 : ∀ (x : Extendedℤ) → (xs : List Extendedℤ) → (x ⊙ xs) ≡ foldl (↑-↓-x x) -∞ xs
minmax-lemma-1 x xs             =  begin
  x ⊙ xs                        ≡⟨ ↓-over-max x xs ⟩
  max (map (x ↓_) xs)           ≡⟨⟩
  foldl _↑_ -∞ (map (x ↓_) xs)  ≡⟨ foldl-map _↑_ (x ↓_) -∞ xs ⟩
  foldl (↑-↓-x x) -∞ xs         ∎

minmax-lemma-2 : ∀ { xss : List (List Extendedℤ)} → minmax-spec xss ≡ foldl _⊙_ +∞ xss
minmax-lemma-2 {xss}            =  begin
   min (map max xss)            ≡⟨⟩
  foldl _↓_ +∞ (map max xss)    ≡⟨ foldl-map _↓_ max +∞ xss ⟩
  foldl _⊙_ +∞ xss              ∎

left-zero-↑-↓-x : ∀ (x : Extendedℤ) → ∀ (u : Extendedℤ) → ↑-↓-x x x u ≡ x
left-zero-↑-↓-x x u rewrite ↑-absorbs-↓ x u = refl

------------------------------------------------------------------------
-- A foldl gets stuck the moment its seed is a left zero of the operation.
foldl-stuck-at-left-zero : ∀ {A : Set} (f : Op₂ A) (z : A)
                         → (∀ y → f z y ≡ z)
                         → ∀ (xs : List A) → foldl f z xs ≡ z
foldl-stuck-at-left-zero f z H [] = refl
foldl-stuck-at-left-zero f z H (x ∷ xs) rewrite H x = foldl-stuck-at-left-zero f z H xs

-- fastfoldl: like foldl, but bails out the moment a decidable predicate fires.
fastfoldl : ∀ {A : Set} {P : A → Set} → Op₂ A → ((z : A) → Dec (P z)) → A → List A → A
fastfoldl f p? e [] = e
fastfoldl f p? e (x ∷ xs) with p? e
... | yes _ = e
... | no  _ = fastfoldl f p? (f e x) xs

-- fastfoldl agrees with foldl when P z guarantees z is a left zero of f.
fastfoldl-spec : ∀ {A : Set} {P : A → Set} (f : Op₂ A) (p? : (z : A) → Dec (P z))
               → (∀ z → P z → ∀ y → f z y ≡ z)
               → ∀ (e : A) (xs : List A)
               → fastfoldl f p? e xs ≡ foldl f e xs
fastfoldl-spec f p? H e [] = refl
fastfoldl-spec f p? H e (x ∷ xs) with p? e
... | yes pe = sym (foldl-stuck-at-left-zero f e (H e pe) (x ∷ xs))
... | no  _  = fastfoldl-spec f p? H (f e x) xs

------------------------------------------------------------------------
-- Decidable equality on Extendedℤ, lifted from ℤ.
_≟ₑ_ : (x y : Extendedℤ) → Dec (x ≡ y)
-∞    ≟ₑ -∞    = yes refl
-∞    ≟ₑ Fin _ = no λ ()
-∞    ≟ₑ +∞    = no λ ()
Fin _ ≟ₑ -∞    = no λ ()
Fin x ≟ₑ Fin y with x Data.Integer.Properties.≟ y
... | yes refl = yes refl
... | no  ¬p   = no λ { refl → ¬p refl }
Fin _ ≟ₑ +∞    = no λ ()
+∞    ≟ₑ -∞    = no λ ()
+∞    ≟ₑ Fin _ = no λ ()
+∞    ≟ₑ +∞    = yes refl

data _<ₑ_ : Extendedℤ → Extendedℤ → Set where
   -∞<ₑ+∞ : -∞ <ₑ +∞ 
   -∞<ₑ : ∀ x → -∞ <ₑ (Fin x)
   x<ₑ+∞ : ∀ x → (Fin x) <ₑ +∞
   Fin<ₑFin : ∀ {x y} → x <ᵢ y → Fin x <ₑ Fin y

infix 4 _<ₑ?_

_<ₑ?_ : Decidable _<ₑ_
-∞ <ₑ? -∞ = no λ ()
-∞ <ₑ? Fin x = yes (-∞<ₑ x)
-∞ <ₑ? +∞ = yes -∞<ₑ+∞
Fin x <ₑ? -∞ = no λ ()
Fin x <ₑ? +∞ = yes (x<ₑ+∞ x)
+∞ <ₑ? y = no λ ()
Fin x <ₑ? Fin y  with x <ᵢ? y
... | yes a = yes (Fin<ₑFin a)
... | no ¬a = no λ {
         (Fin<ₑFin x) → ¬a x
     } 

αβ : Extendedℤ → List Extendedℤ → Extendedℤ
αβ x xs = fastfoldl (↑-↓-x x) (_≟ₑ x) -∞ xs

αβ-correct : ∀ (x : Extendedℤ) (xs : List Extendedℤ) → αβ x xs ≡ foldl (↑-↓-x x) -∞ xs
αβ-correct x xs = fastfoldl-spec (↑-↓-x x) (_≟ₑ x) lz -∞ xs
  where
    lz : ∀ z → z ≡ x → ∀ y → ↑-↓-x x z y ≡ z
    lz z refl y = ↑-absorbs-↓ x y

⊙≡αβ : ∀ (x : Extendedℤ) (xs : List Extendedℤ) → x ⊙ xs ≡ αβ x xs
⊙≡αβ x xs = trans (minmax-lemma-1 x xs) (sym (αβ-correct x xs))


-- The alpha-beta algorithm and its correctness theorem.
alphabeta : List (List Extendedℤ) → Extendedℤ
alphabeta = foldl αβ +∞

alphabeta-correct : ∀ (xss : List (List Extendedℤ)) → minmax-spec xss ≡ alphabeta xss
alphabeta-correct xss = begin
  minmax-spec xss            ≡⟨ minmax-lemma-2 {xss} ⟩
  foldl _⊙_ +∞ xss           ≡⟨ foldl-cong ⊙≡αβ +∞ xss ⟩
  foldl αβ +∞ xss            ≡⟨⟩
  alphabeta xss              ∎


{-
data GameTree (A : Set) : Set where
  Leaf : A → GameTree A
  Node : List (GameTree A) → GameTree A


-- Given a game tree, we want to find the best move for the first player. That is which of its successor nodes should it move to.
-- That is, the highest value of all the leaves that the start player can reach, no matter what the opponent plays.
-- On his part, the opponent will try to minimize the value of the leaf that the start player can reach.
-- In other words, we have a maximizing player and a minimizing player, and we want to find the best move for the maximizing player.

mutual
   maxmin : GameTree Extendedℤ → Extendedℤ
   maxmin (Leaf v) = v
   maxmin (Node ts) = maxs ts

   minmax : GameTree Extendedℤ → Extendedℤ
   minmax (Leaf v) = v
   minmax (Node ts) = mins ts

   maxs : List (GameTree Extendedℤ) → Extendedℤ
   maxs [] = -∞
   maxs (t ∷ ts) = (minmax t) ↑ maxs ts


   mins : List (GameTree Extendedℤ) → Extendedℤ
   mins [] = +∞
   mins (t ∷ ts) = (maxmin t) ↓ mins ts 


mutual
  αβ-max : Extendedℤ → Extendedℤ → GameTree Extendedℤ → Extendedℤ
  αβ-max _ _ (Leaf v) = v
  αβ-max α β (Node ts) = αβ-maxs α β ts

  αβ-maxs : Extendedℤ → Extendedℤ → List (GameTree Extendedℤ) → Extendedℤ
  αβ-maxs α _ [] = α
  αβ-maxs α β (t ∷ ts) with α ↑ (αβ-min α β t)
  ... | α′ with β <ₑ? α′
  ... | no ¬a = αβ-maxs α′ β ts 
  ... | yes a = α′

  αβ-min : Extendedℤ → Extendedℤ → GameTree Extendedℤ → Extendedℤ
  αβ-min _ _ (Leaf v) = v
  αβ-min α β (Node ts) = αβ-mins α β ts

  αβ-mins : Extendedℤ → Extendedℤ → List (GameTree Extendedℤ) → Extendedℤ
  αβ-mins _ β [] = β
  αβ-mins α β (t ∷ ts) with β ↓ (αβ-max α β t )
  ... | β' with β' <ₑ? α
  ... | no ¬a = αβ-mins α β' ts
  ... | yes a = β'

-}
