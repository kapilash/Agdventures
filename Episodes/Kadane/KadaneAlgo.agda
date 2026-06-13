{-# OPTIONS --safe #-}
module KadaneAlgo where

open import Data.Integer renaming ( _⊔_ to _⊔ᵢ_ ; _⊓_ to _⊓ᵢ_  ; _+_ to _+ᵢ_; _*_ to _*ᵢ_)
open import Data.Integer.Properties
open import Data.List
open import Data.List.Properties using (++-isMonoid ; foldl-++ ; foldl-map ;  concat-map ;  map-∘ ;  map-cong ; map-cong-local)
open import Data.List.Scans.Properties using (scanl-defn ; scanr-defn)
open import Data.Nat renaming (_⊔_ to _⊔ₙ_ ; _⊓_ to _⊓ₙ_)
open import Data.Sum hiding (map)
open import Data.Product hiding (map)
open import Relation.Nullary.Negation
open import Relation.Nullary.Decidable hiding (map)
import Relation.Binary.PropositionalEquality as Eq
open Eq
open Eq.≡-Reasoning
open import Function using (id ; _∘_)
open import Algebra
open import Relation.Binary using (IsEquivalence)
open import Algebra.Properties.Monoid


foldl-accumulator : ∀ {A : Set} {f : Op₂ A} {ϵ : A} → (IsMonoid {A = A} _≡_ f ϵ) → (a : A) → (xs : List A) → foldl f a xs ≡ f a (foldl f ϵ xs)
foldl-accumulator {A} {f} {ϵ} ismonoid a [] = sym (proj₂ (IsMonoid.identity ismonoid) a)
foldl-accumulator {A} {f} {ϵ} ismonoid a (y ∷ xs) = begin
  foldl f (f a y) xs                              ≡⟨ foldl-accumulator ismonoid (f a y) xs ⟩
  f (f a y) (foldl f ϵ xs)                        ≡⟨ IsSemigroup.assoc (IsMonoid.isSemigroup ismonoid) a y (foldl f ϵ xs) ⟩
  f a (f y (foldl f ϵ xs))                        ≡⟨ cong (f a) (sym (foldl-accumulator ismonoid y xs)) ⟩
  f a (foldl f y xs)                              ≡⟨ cong (λ k → f a (foldl f k xs)) (sym (proj₁ (IsMonoid.identity ismonoid) y)) ⟩
  f a (foldl f (f ϵ y) xs)                        ≡⟨⟩
  f a (foldl f ϵ (y ∷ xs))                        ∎

foldl-head : ∀ {A : Set} {f : Op₂ A} {ϵ : A} → (IsMonoid {A = A} _≡_ f ϵ) → (x : A) → (xs : List A) → foldl f ϵ (x ∷ xs) ≡ f x (foldl f ϵ xs)
foldl-head {A} {f} {ϵ} ismonoid x xs               =  begin
  foldl f (f ϵ x) xs                               ≡⟨ cong (λ k → foldl f k xs) (proj₁ (IsMonoid.identity ismonoid) x ) ⟩
  foldl f x xs                                     ≡⟨ foldl-accumulator ismonoid x xs ⟩
  f x (foldl f ϵ xs)                               ∎

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

infixl 6 _↑_
infixl 6 _+ₑ_
infixl 8 _*ₑ_

_↑_ : Extendedℤ → Extendedℤ → Extendedℤ
-∞ ↑ y = y
Fin x ↑ -∞ = Fin x
Fin x ↑ Fin y = Fin ( x ⊔ᵢ y)


_+ₑ_ : Extendedℤ → Extendedℤ → Extendedℤ
-∞ +ₑ y = -∞
Fin x +ₑ -∞ = -∞
Fin x +ₑ Fin y = Fin (x +ᵢ y )

0ₑ : Extendedℤ
0ₑ = Fin 0ℤ

1ₑ : Extendedℤ
1ₑ = Fin 1ℤ

_*ₑ_ : Extendedℤ → Extendedℤ → Extendedℤ
-∞ *ₑ y = -∞
Fin x *ₑ -∞ = -∞
Fin x *ₑ Fin y = Fin (x *ᵢ y)


+ₑ-identityʳ : ∀ (x : Extendedℤ) → x +ₑ 0ₑ ≡ x
+ₑ-identityʳ -∞ = refl
+ₑ-identityʳ (Fin x) rewrite +-identityʳ x = refl

+ₑ-identityˡ : ∀ (x : Extendedℤ) → 0ₑ +ₑ x ≡ x
+ₑ-identityˡ -∞ = refl
+ₑ-identityˡ (Fin x) rewrite +-identityˡ x = refl

+ₑ-comm : ∀ (x y : Extendedℤ) → x +ₑ y ≡ y +ₑ x
+ₑ-comm -∞ -∞ = refl
+ₑ-comm -∞ (Fin x) = refl
+ₑ-comm (Fin x) -∞ = refl
+ₑ-comm (Fin x) (Fin y) rewrite +-comm x y = refl


+ₑ-assoc : ∀ (x y z : Extendedℤ) → (x +ₑ y) +ₑ z ≡ x +ₑ (y +ₑ z)
+ₑ-assoc -∞ y z = refl
+ₑ-assoc (Fin x) -∞ z = refl
+ₑ-assoc (Fin x) (Fin y) -∞ = refl
+ₑ-assoc (Fin x) (Fin y) (Fin z) rewrite +-assoc x y z = refl

+ₑ-distribʳ-↑ : ∀ (x y z : Extendedℤ) → (x ↑ y) +ₑ z ≡ (x +ₑ z) ↑ (y +ₑ z)
+ₑ-distribʳ-↑ -∞ -∞ -∞ = refl
+ₑ-distribʳ-↑ -∞ -∞ (Fin z) = refl
+ₑ-distribʳ-↑ -∞ (Fin y) -∞ = refl
+ₑ-distribʳ-↑ -∞ (Fin y) (Fin z) = refl
+ₑ-distribʳ-↑ (Fin x) -∞ -∞ = refl
+ₑ-distribʳ-↑ (Fin x) -∞ (Fin z) = refl
+ₑ-distribʳ-↑ (Fin x) (Fin y) -∞ = refl
+ₑ-distribʳ-↑ (Fin x) (Fin y) (Fin z) rewrite mono-≤-distrib-⊔ (+-monoˡ-≤ z) x y = refl


*ₑ-identityʳ : ∀ (x : Extendedℤ) → x *ₑ 1ₑ ≡ x
*ₑ-identityʳ -∞ = refl
*ₑ-identityʳ (Fin x) rewrite *-identityʳ x = refl

*ₑ-identityˡ : ∀ (x : Extendedℤ) → 1ₑ *ₑ x ≡ x
*ₑ-identityˡ -∞ = refl
*ₑ-identityˡ (Fin x) rewrite *-identityˡ x = refl

*ₑ-comm : ∀ (x y : Extendedℤ) → x *ₑ y ≡ y *ₑ x
*ₑ-comm -∞ -∞ = refl
*ₑ-comm -∞ (Fin x) = refl
*ₑ-comm (Fin x) -∞ = refl
*ₑ-comm (Fin x) (Fin y) rewrite *-comm x y = refl


*ₑ-assoc : ∀ (x y z : Extendedℤ) → (x *ₑ y) *ₑ z ≡ x *ₑ (y *ₑ z)
*ₑ-assoc -∞ y z = refl
*ₑ-assoc (Fin x) -∞ z = refl
*ₑ-assoc (Fin x) (Fin y) -∞ = refl
*ₑ-assoc (Fin x) (Fin y) (Fin z) rewrite *-assoc x y z = refl


+ₑ-isMagma : IsMagma {A = Extendedℤ} _≡_ _+ₑ_
+ₑ-isMagma = record { isEquivalence = Eq.isEquivalence ; ∙-cong = cong₂ _+ₑ_  }

+ₑ-isSemigroup : IsSemigroup {A = Extendedℤ} _≡_ _+ₑ_
+ₑ-isSemigroup = record { isMagma = +ₑ-isMagma ; assoc = +ₑ-assoc }

+ₑ-isMonoid : IsMonoid {A = Extendedℤ} _≡_ _+ₑ_ 0ₑ
+ₑ-isMonoid = record { isSemigroup = +ₑ-isSemigroup ; identity = +ₑ-identityˡ , +ₑ-identityʳ }

*ₑ-isMagma : IsMagma {A = Extendedℤ} _≡_ _*ₑ_
*ₑ-isMagma = record { isEquivalence = Eq.isEquivalence ; ∙-cong = cong₂ _*ₑ_  }

*ₑ-isSemigroup : IsSemigroup {A = Extendedℤ} _≡_ _*ₑ_
*ₑ-isSemigroup = record { isMagma = *ₑ-isMagma ; assoc = *ₑ-assoc }

*ₑ-isMonoid : IsMonoid {A = Extendedℤ} _≡_ _*ₑ_ 1ₑ
*ₑ-isMonoid = record { isSemigroup = *ₑ-isSemigroup ; identity = *ₑ-identityˡ , *ₑ-identityʳ }


↑-assoc : ∀ (x y z : Extendedℤ) →  (x ↑ y) ↑ z ≡ x ↑ (y ↑ z)
↑-assoc -∞ y z = refl
↑-assoc (Fin x) -∞ z = refl
↑-assoc (Fin x) (Fin y) -∞ = refl
↑-assoc (Fin x) (Fin y) (Fin z) rewrite ⊔-assoc x y z = refl


↑-identityʳ : ∀ (x : Extendedℤ) → x ↑ -∞ ≡ x
↑-identityʳ -∞ = refl
↑-identityʳ (Fin x) = refl

↑-identityˡ : ∀ (x : Extendedℤ) → -∞ ↑ x ≡ x
↑-identityˡ x = refl


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

max : List Extendedℤ → Extendedℤ
max = foldl _↑_ -∞

sumₑ : List Extendedℤ → Extendedℤ
sumₑ lst = foldl _+ₑ_ 0ₑ lst

sumₑ-head : ∀ (x : Extendedℤ) (xs : List Extendedℤ) → sumₑ (x ∷ xs) ≡ x +ₑ sumₑ xs
sumₑ-head x xs = foldl-head +ₑ-isMonoid x xs

{-  returns list of all segments of a given list -}
segs  : List Extendedℤ → List (List Extendedℤ)
segs  = concat ∘ map tails ∘ inits

mss-spec : List Extendedℤ → Extendedℤ
mss-spec = max ∘ map sumₑ ∘  segs

mss-f : Extendedℤ × Extendedℤ → Extendedℤ → Extendedℤ × Extendedℤ
mss-f (u , v) x = (u ↑ ( (v +ₑ x ) ↑ 0ₑ)) , ((v +ₑ x) ↑ 0ₑ)

mss-impl :  List Extendedℤ → Extendedℤ
mss-impl lst = proj₁ (foldl mss-f (0ₑ , 0ₑ) lst )


fsf-f : Op₂ Extendedℤ → Op₂ Extendedℤ → Extendedℤ × Extendedℤ → Extendedℤ → Extendedℤ × Extendedℤ
fsf-f f g (u , v) x  = f u (g v x) , g v x

{-  function for getting horner rule via foldl  -}
hf : Extendedℤ → Extendedℤ → Extendedℤ
hf x y = (x +ₑ y) ↑ 0ₑ

fold-scan-fusion : (f g : Op₂ Extendedℤ) → ∀ (a b : Extendedℤ) → (xs : List Extendedℤ) → foldl f a (scanl g b xs) ≡ proj₁ (foldl (fsf-f f g) (f a b , b) xs)
fold-scan-fusion f g a b [] = refl
fold-scan-fusion f g a b (x ∷ xs) = fold-scan-fusion f g (f a b) (g b x) xs


{- generalised form: starting from any `a ↑ 0ₑ` accumulator the running max-prefix-or-0
   factors as the total sum (shifted by `a`) joined with the result for the rest. -}
gen-hf-lemma : ∀ (a : Extendedℤ) (xs : List Extendedℤ)
             → foldl hf (a ↑ 0ₑ) xs ≡ (a +ₑ sumₑ xs) ↑ foldl hf 0ₑ xs
gen-hf-lemma a [] = cong (_↑ 0ₑ) (sym (+ₑ-identityʳ a))
gen-hf-lemma a (y ∷ ys) = begin
  foldl hf (a ↑ 0ₑ) (y ∷ ys)
    ≡⟨⟩
  foldl hf (((a ↑ 0ₑ) +ₑ y) ↑ 0ₑ) ys
    ≡⟨ cong (λ k → foldl hf (k ↑ 0ₑ) ys) (+ₑ-distribʳ-↑ a 0ₑ y) ⟩
  foldl hf (((a +ₑ y) ↑ (0ₑ +ₑ y)) ↑ 0ₑ) ys
    ≡⟨ cong (λ k → foldl hf (((a +ₑ y) ↑ k) ↑ 0ₑ) ys) (+ₑ-identityˡ y) ⟩
  foldl hf (((a +ₑ y) ↑ y) ↑ 0ₑ) ys
    ≡⟨ gen-hf-lemma ((a +ₑ y) ↑ y) ys ⟩
  (((a +ₑ y) ↑ y) +ₑ sumₑ ys) ↑ foldl hf 0ₑ ys
    ≡⟨ cong (_↑ foldl hf 0ₑ ys) (+ₑ-distribʳ-↑ (a +ₑ y) y (sumₑ ys)) ⟩
  (((a +ₑ y) +ₑ sumₑ ys) ↑ (y +ₑ sumₑ ys)) ↑ foldl hf 0ₑ ys
    ≡⟨ ↑-assoc ((a +ₑ y) +ₑ sumₑ ys) (y +ₑ sumₑ ys) (foldl hf 0ₑ ys) ⟩
  ((a +ₑ y) +ₑ sumₑ ys) ↑ ((y +ₑ sumₑ ys) ↑ foldl hf 0ₑ ys)
    ≡⟨ cong (_↑ ((y +ₑ sumₑ ys) ↑ foldl hf 0ₑ ys)) (+ₑ-assoc a y (sumₑ ys)) ⟩
  (a +ₑ (y +ₑ sumₑ ys)) ↑ ((y +ₑ sumₑ ys) ↑ foldl hf 0ₑ ys)
    ≡⟨ cong (λ k → (a +ₑ k) ↑ ((y +ₑ sumₑ ys) ↑ foldl hf 0ₑ ys)) (sym (sumₑ-head y ys)) ⟩
  (a +ₑ sumₑ (y ∷ ys)) ↑ ((y +ₑ sumₑ ys) ↑ foldl hf 0ₑ ys)
    ≡⟨ cong ((a +ₑ sumₑ (y ∷ ys)) ↑_) (sym (gen-hf-lemma y ys)) ⟩
  (a +ₑ sumₑ (y ∷ ys)) ↑ foldl hf (y ↑ 0ₑ) ys
    ≡⟨ cong (λ k → (a +ₑ sumₑ (y ∷ ys)) ↑ foldl hf (k ↑ 0ₑ) ys) (sym (+ₑ-identityˡ y)) ⟩
  (a +ₑ sumₑ (y ∷ ys)) ↑ foldl hf ((0ₑ +ₑ y) ↑ 0ₑ) ys
    ≡⟨⟩
  (a +ₑ sumₑ (y ∷ ys)) ↑ foldl hf 0ₑ (y ∷ ys)
  ∎


horners-lemma : ∀ (x : Extendedℤ) → (xs : List Extendedℤ)  → foldl hf 0ₑ (x ∷ xs) ≡  (sumₑ (x ∷ xs)) ↑ (foldl hf 0ₑ xs)
horners-lemma x xs  = begin
  foldl hf 0ₑ (x ∷ xs)                                            ≡⟨⟩
  foldl hf ((0ₑ +ₑ x) ↑ 0ₑ) xs                                    ≡⟨ cong (λ k → foldl hf (k ↑ 0ₑ) xs) (+ₑ-identityˡ x) ⟩
  foldl hf (x ↑ 0ₑ) xs                                            ≡⟨ gen-hf-lemma x xs ⟩
  (x +ₑ sumₑ xs) ↑ foldl hf 0ₑ xs                                 ≡⟨ cong (_↑ foldl hf 0ₑ xs) (sym (sumₑ-head x xs)) ⟩
  sumₑ (x ∷ xs) ↑ foldl hf 0ₑ xs                                  ∎


horners-rule : (xs : List Extendedℤ) → max (map sumₑ (tails xs)) ≡ foldl hf 0ₑ xs
horners-rule [] = refl
horners-rule (x ∷ xs)         =  begin
  max (map sumₑ (tails (x ∷ xs)))                   ≡⟨⟩
  max (map sumₑ ((x ∷ xs) ∷ tails xs))              ≡⟨⟩
  max (sumₑ (x ∷ xs) ∷ map sumₑ (tails xs))         ≡⟨ foldl-head ↑-isMonoid (sumₑ (x ∷ xs)) (map sumₑ (tails xs)) ⟩
  (sumₑ (x ∷ xs)) ↑ (max (map sumₑ (tails xs)))     ≡⟨ cong (λ k → (sumₑ (x ∷ xs)) ↑ k) (horners-rule xs)   ⟩
  (sumₑ (x ∷ xs)) ↑ foldl hf 0ₑ xs                  ≡⟨ sym (horners-lemma x xs) ⟩
  foldl hf 0ₑ  (x ∷ xs)                             ∎


mss-theorem : ∀ (xs : List Extendedℤ) → mss-spec xs ≡ mss-impl xs
mss-theorem xs                                                                = begin
  (max ∘ map sumₑ ∘  segs) xs                                                 ≡⟨⟩
  (max ∘ map sumₑ ∘ concat ∘ map tails ∘ inits) xs                            ≡⟨ cong max (sym (concat-map (map tails (inits xs)))) ⟩
  (max ∘ concat ∘ map (map sumₑ) ∘ map tails ∘ inits ) xs                     ≡⟨⟩
  (max ∘ concat ∘ map (map sumₑ) ∘ map tails ∘ inits ) xs            ≡⟨ fold-promotion ↑-isMonoid ( map (map sumₑ) ( map tails (inits xs ))) ⟩
  (max ∘ map (foldl _↑_ -∞) ∘ map (map sumₑ) ∘ map tails ∘ inits) xs ≡⟨⟩
  (max ∘ map max ∘ map (map sumₑ) ∘ map tails ∘ inits) xs                     ≡⟨ cong max (sym (map-∘ ( map tails (inits xs))))  ⟩
  (max ∘ map (max ∘ map sumₑ) ∘ map tails ∘ inits) xs                         ≡⟨ cong  max (sym (map-∘ (inits xs))) ⟩
  (max ∘ map (max ∘ map sumₑ ∘ tails) ∘ inits) xs                             ≡⟨ cong max (map-cong horners-rule (inits xs)) ⟩
  (max ∘ map (foldl hf 0ₑ) ∘ inits) xs                                        ≡⟨ cong max (sym ( scanl-defn hf 0ₑ  xs ))⟩
  (max ∘ scanl hf 0ₑ) xs                                                      ≡⟨⟩
  (foldl _↑_ -∞ ∘ scanl hf 0ₑ) xs                                             ≡⟨ fold-scan-fusion _↑_ hf  -∞ 0ₑ xs ⟩
  (proj₁ ∘ foldl mss-f (0ₑ , 0ₑ)) xs                                          ∎
