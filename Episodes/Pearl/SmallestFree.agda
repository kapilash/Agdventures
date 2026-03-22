{-# OPTIONS --safe #-}
module SmallestFree where

open import Data.Nat
open import Data.Bool hiding ( _<?_; _≟_; _<_ )
open import Data.Nat.Properties
open import Data.Bool.Properties hiding ( _<?_; _≟_ )
open import Data.List
open import Data.List.Properties
open import Data.Empty
open import Data.Maybe
open import Data.Product
open import Data.Sum
open import Relation.Nullary.Negation
open import Relation.Nullary.Decidable
import Relation.Binary.PropositionalEquality as Eq
open Eq
open Eq.≡-Reasoning using (begin_; step-≡-∣; step-≡-⟩; _∎)
open import Function.Base using (_∘_)
open import Level using ( _⊔_ ; Level; 0ℓ)
open import Relation.Nullary.Reflects
open import Agda.Builtin.Unit
open import Data.Unit.Base using (⊤)
open import Relation.Unary hiding (_\\_)
open import Relation.Unary.Properties using (_∩?_ ; _×?_ ; does-≐; ∁? )
open import Data.List.Relation.Unary.All hiding (head)
open import Data.List.NonEmpty renaming (head to head⁺; tail to tail⁺; toList to list⁺→List ; length to length⁺; _∷_ to cons⁺ ) hiding (reverse)

data _∉ₙ_  : ℕ →  List ℕ → Set  where
   notin-nil  : ∀ n →  n ∉ₙ []
   notin-cons : ∀ {n x xs} → ¬ (n ≡ x) → ( n ∉ₙ xs) → n ∉ₙ (x ∷ xs)

nothead : ∀ {n x xs} → n ∉ₙ (x ∷ xs) → ¬ (n ≡ x)
nothead (notin-cons ¬eq _) eq = ¬eq eq

head⇒¬∉ₙ : ∀ {x xs}  → ¬(x ∉ₙ (x ∷ xs))
head⇒¬∉ₙ {x} {xs} (notin-cons x₁ notnotin) = x₁ refl

notintail : ∀ {n x xs} → n ∉ₙ (x ∷ xs) → n ∉ₙ xs
notintail (notin-cons ¬eq notin-xs) = notin-xs

intail⇒¬∉ₙ : ∀ {n x xs} → ¬(n ∉ₙ xs) → ¬ (n ∉ₙ (x ∷ xs))
intail⇒¬∉ₙ {n} {x} {xs} notintail (notin-cons x₁ x₂) = notintail x₂

n≢x⇒notin : ∀ {n x xs} → ¬ (n ≡ x) → n ∉ₙ xs → n ∉ₙ (x ∷ xs)
n≢x⇒notin ¬eq notin-xs = notin-cons ¬eq notin-xs

notin? : (n : ℕ) → (lst : List ℕ) → Dec (n ∉ₙ lst)
notin? n [] = yes (notin-nil n)
notin? n (x ∷ lst) with (n ≟ x) | (notin? n lst)
... | no ¬a | no ¬l = no (λ x₁ →  ¬l  (notintail x₁) )
... | no ¬a | yes l = yes (notin-cons {n} {x} {lst} ¬a l)
... | yes a | no ¬l = no (λ x₁ → ¬l (notintail x₁))
... | yes a | yes l = no ( λ x₁ → (nothead x₁) a )


∉ₙ-++ : ∀ {n l₁ l₂} → n ∉ₙ l₁ → n ∉ₙ l₂ → n ∉ₙ (l₁ ++ l₂)
∉ₙ-++ {n} {[]} {l₂} notin-l1 notin-l2 = notin-l2
∉ₙ-++ {n} {x ∷ l₁} {l₂} (notin-cons x₁ notin-l1) notin-l2 = notin-cons x₁  (∉ₙ-++ {n} {l₁} {l₂} notin-l1 notin-l2 )


∉ₙ-split-1 : ∀ {n l₁ l₂} → n ∉ₙ (l₁ ++ l₂) → n ∉ₙ l₁
∉ₙ-split-1 {n} {[]} {l₂} notin = notin-nil n
∉ₙ-split-1 {n} {x ∷ l₁} {l₂} (notin-cons x₁ notin) = notin-cons x₁ (∉ₙ-split-1 notin)

∉ₙ-split-2 : ∀ {n l₁ l₂} → n ∉ₙ (l₁ ++ l₂) → n ∉ₙ l₂
∉ₙ-split-2 {n} {[]} {l₂} notin = notin
∉ₙ-split-2 {n} {x ∷ l₁} {l₂} (notin-cons x₁ notin) =  ∉ₙ-split-2 notin


∉ₙ-split-insert : ∀ {x₁ x₂ l₁ l₂} → (x₁ ∉ₙ (l₁ ++ l₂)) → ¬ (x₁ ≡ x₂) → (x₁ ∉ₙ (l₁ ++ x₂ ∷ l₂))
∉ₙ-split-insert {x₁} {x₂} {l₁} {l₂} union ¬eq =  ∉ₙ-++ {x₁} {l₁} {x₂ ∷ l₂}  (∉ₙ-split-1  {x₁} {l₁} {l₂} union ) (notin-cons ¬eq (∉ₙ-split-2 {x₁} {l₁} {l₂}  union))


∉ₙ-++-comm : ∀ {x l₁ l₂} → (x ∉ₙ (l₁ ++ l₂)) → (x ∉ₙ (l₂ ++ l₁))
∉ₙ-++-comm {x} {[]} {l₂} union rewrite (++-identityʳ l₂) = union
∉ₙ-++-comm {x} {x₁ ∷ l₁} {l₂} (notin-cons x₂ union) =    ∉ₙ-split-insert {x} {x₁} {l₂} {l₁} (∉ₙ-++-comm {x} {l₁} {l₂} union) x₂

_\\_ : List ℕ → List ℕ → List ℕ
xs \\ ys = filter (λ k → notin? k  ys) xs

filter-and≡filter-++ : ∀ {l₁ l₂ l} → filter (λ k → notin? k l₂  ×-dec notin? k l₁) l ≡ filter (λ k → notin? k (l₂ ++ l₁)) l
filter-and≡filter-++ {l₁} {l₂} {l} = filter-≐ 
                             (λ k → notin? k l₂  ×-dec notin? k l₁)
                             (λ k → notin? k (l₂ ++ l₁))
                             (uncurry ∉ₙ-++ , λ k → (∉ₙ-split-1 k , ∉ₙ-split-2 k ))
                             l

filter-++-comm : ∀ {l₁ l₂ l} → filter (λ k → notin? k (l₂ ++ l₁)) l ≡ filter (λ k → notin? k (l₁ ++ l₂)) l
filter-++-comm {l₁} {l₂} {l} = filter-≐ 
                               (λ k → notin? k (l₂ ++ l₁))
                               (λ k → notin? k (l₁ ++ l₂))
                               (∉ₙ-++-comm   {l₁ = l₂} {l₁} , ∉ₙ-++-comm {l₁ = l₁} {l₂})
                               l

filter-notin-comm : ∀ {l₁ l₂ l} →  filter (λ k → notin? k l₂  ×-dec notin? k l₁) l ≡ filter (λ k → notin? k l₁  ×-dec notin? k l₂) l
filter-notin-comm {l₁} {l₂} {l} = filter-≐
                                  (λ k → notin? k l₂  ×-dec notin? k l₁)
                                  (λ k → notin? k l₁  ×-dec notin? k l₂)
                                  ((λ {x} z → z .proj₂ , z .proj₁) , (λ {x} z → z .proj₂ , z .proj₁))
                                  l

smallestFree-spec1 : List ℕ → Maybe ℕ
smallestFree-spec1 lst = head (upTo (suc (length lst)) \\ lst)


smallestFree-spec2 : List⁺ ℕ → ℕ
smallestFree-spec2 lst with head (upTo (suc (length⁺ lst))  \\ ( list⁺→List lst ))
... | just x = x
... | nothing = sfn (head⁺ lst)
 where sfn : ℕ → ℕ
       sfn zero = suc zero
       sfn (suc n) = zero


empty-\\ : ∀ {l} → [] \\ l ≡ []
empty-\\ {l} = refl

\\-empty : ∀ {l} → l \\ [] ≡ l
\\-empty {[]} = refl
\\-empty {x ∷ l}                            = begin
   (x ∷ l) \\ []                            ≡⟨⟩
   filter (λ k → notin? k []) (x ∷ l)       ≡⟨⟩
   x ∷ (filter (λ k → notin? k []) l )      ≡⟨⟩
   x ∷ (l \\ [])                            ≡⟨ cong (λ k → x ∷ k) ( \\-empty {l}) ⟩
   x ∷ l                                    ∎

∷ˡ-\\ : ∀ {x l₁ l₂} → (x ∷ l₁) \\ l₂ ≡ ((x ∷ []) \\ l₂) ++ (l₁ \\ l₂)
∷ˡ-\\ {x} {l₁} {l₂} with (notin? x l₂ )
... | no ¬a = refl
... | yes a = refl


++-\\ : ∀ {as bs cs} → ((as ++ bs ) \\ cs) ≡ (as \\ cs) ++ (bs \\ cs)
++-\\ {[]} {bs} {cs} = refl
++-\\ {x ∷ as} {bs} {cs} = begin
 (((x ∷ as) ++ bs) \\ cs)                       ≡⟨⟩
 ((x ∷ (as ++ bs)) \\ cs)                       ≡⟨ ∷ˡ-\\ {x} {as ++ bs} ⟩
 ((x ∷ []) \\ cs) ++ ((as ++ bs) \\ cs)         ≡⟨ cong (λ k → ((x ∷ []) \\ cs) ++ k)  (++-\\ {as} {bs} {cs}) ⟩
 ((x ∷ []) \\ cs) ++ (as \\ cs) ++ (bs \\ cs)   ≡⟨ sym (++-assoc ((x ∷ []) \\ cs)  (as \\ cs) (bs \\ cs)) ⟩
 (((x ∷ []) \\ cs) ++ (as \\ cs)) ++ (bs \\ cs) ≡⟨ cong (λ k → k ++ (bs \\ cs)) ( sym ( ∷ˡ-\\ {x} {as} )) ⟩
 ((x ∷ as) \\ cs) ++ (bs \\ cs)                 ∎

filter-∘-filter : ∀ {a p q} {A : Set a} {P  : Pred A p} {Q : Pred A q} (P? : Decidable P) (Q? : Decidable Q) (xs : List A) →
                filter P? (filter Q? xs) ≡ filter (P? ∩? Q?) xs
filter-∘-filter P? Q? [] = refl
filter-∘-filter P? Q? (x ∷ l) with Q? x
filter-∘-filter P? Q? (x ∷ l) | no ¬q  with P? x
filter-∘-filter P? Q? (x ∷ l) | no ¬q | no ¬p = filter-∘-filter P? Q? l
filter-∘-filter P? Q? (x ∷ l) | no ¬q | yes p = filter-∘-filter P? Q? l
filter-∘-filter P? Q? (x ∷ l) | yes q with P? x
filter-∘-filter P? Q? (x ∷ l) | yes q | no ¬p rewrite (filter-∘-filter P? Q? l) = refl
filter-∘-filter P? Q? (x ∷ l) | yes q | yes p rewrite (filter-∘-filter P? Q? l)  = refl

\\-++ : ∀ {l l₁ l₂} → ((l \\ l₁) \\ l₂ ≡ l \\ (l₁ ++ l₂))
\\-++ {l} {l₁} {l₂}                                               =  begin
    (l \\ l₁) \\ l₂                                               ≡⟨⟩
    filter (λ k → notin? k l₂) (l \\ l₁)                          ≡⟨⟩
    filter (λ k → notin? k l₂) (filter  (λ k → notin? k l₁)  l)   ≡⟨ filter-∘-filter (λ x → notin? x l₂) (λ k → notin? k l₁)  l ⟩
    filter (λ k → notin? k l₂  ×-dec notin? k l₁) l               ≡⟨ filter-and≡filter-++ {l₁} {l₂} {l} ⟩
    filter (λ k → notin? k (l₂ ++ l₁))  l                         ≡⟨ filter-++-comm {l₁} {l₂} {l} ⟩
    filter (λ k → notin? k (l₁ ++ l₂)) l                          ≡⟨⟩
     l \\ (l₁ ++ l₂)                                              ∎

\\-\\ : ∀ {l l₁ l₂} → ((l \\ l₁) \\ l₂) ≡ ((l \\ l₂) \\ l₁)
\\-\\ {l} {l₁} {l₂}                                              = begin
   (l \\ l₁) \\ l₂                                               ≡⟨⟩
   filter (λ k → notin? k l₂) (l \\ l₁)                          ≡⟨⟩
   filter  (λ k → notin? k l₂) (filter  (λ k → notin? k l₁)  l)  ≡⟨ filter-∘-filter (λ x → notin? x l₂) (λ k → notin? k l₁)  l ⟩
   filter (λ k → notin? k l₂  ×-dec notin? k l₁) l               ≡⟨ filter-notin-comm {l₁} {l₂} {l}⟩
   filter (λ k → notin? k l₁  ×-dec notin? k l₂) l               ≡⟨ sym (filter-∘-filter (λ x → notin? x l₁) (λ k → notin? k l₂)  l) ⟩
   filter (λ k → notin? k l₁) (filter  (λ k → notin? k l₂)  l)   ≡⟨⟩
    filter (λ k → notin? k l₁) (l \\ l₂)                         ≡⟨⟩
     (l \\ l₂) \\ l₁                                             ∎

record Disjoint (l₁ l₂ : List ℕ) : Set where
  constructor disjoint
  field
    proof₁ : ∀ n  →  ¬(n ∉ₙ l₁) → (n ∉ₙ l₂)
    proof₂ : ∀ n  →  ¬(n ∉ₙ l₂) → (n ∉ₙ l₁)

disjoint-tail1 : ∀ {x l₁ l₂} → Disjoint (x ∷ l₁) l₂ → Disjoint l₁ l₂
disjoint-tail1 {x} {l₁} {l₂} (disjoint proof₁ proof₂) = disjoint helper1   helper2
   where
    helper1 : ∀ n → ¬(n ∉ₙ l₁) → n ∉ₙ l₂
    helper1 n inl₁ = proof₁ n (intail⇒¬∉ₙ {n} {x} {l₁} inl₁ )

    helper2 : ∀ n → ¬(n ∉ₙ l₂) → n ∉ₙ l₁
    helper2 n inl₂ = notintail (proof₂ n inl₂)

empty-disjoint : Disjoint [] []
empty-disjoint = disjoint (λ n z → notin-nil n) (λ n z → notin-nil n)

empty-disjoint-left : ∀ {l} → Disjoint [] l
empty-disjoint-left {[]} = disjoint (λ n z → notin-nil n) (λ n z → notin-nil n)
empty-disjoint-left {x ∷ l} = disjoint
                               (λ n z →
                                  notin-cons (λ z₁ → z (notin-nil n))
                                  (empty-disjoint-left .Disjoint.proof₁ n z))
                               (λ n z → notin-nil n)

disjoint-lemma : ∀ {l₁ l₂} → Disjoint l₁ l₂ → (l₁ \\ l₂) ≡ l₁
disjoint-lemma {[]} {l₂} d = refl
disjoint-lemma {x ∷ l₁} {l₂} (disjoint proof₁ proof₂) with notin? x l₂
... | no ¬a =  contradiction-irr ((proof₂ x ¬a)) (head⇒¬∉ₙ {x} {l₁}) -- {! ?!}
... | yes a  = cong (λ p → x ∷ p) (disjoint-lemma {l₁} {l₂} (disjoint helper1 helper2) )
   where
    helper1 : ∀ n → ¬(n ∉ₙ l₁) → n ∉ₙ l₂
    helper1 n inl₁ = proof₁ n (intail⇒¬∉ₙ {n} {x} {l₁} inl₁ )

    helper2 : ∀ n → ¬(n ∉ₙ l₂) → n ∉ₙ l₁
    helper2 n inl₂ = notintail (proof₂ n inl₂)

disjoint-diff : ∀ {as bs us vs} → Disjoint as vs → Disjoint bs us →   (as ++ bs ) \\ (us ++ vs) ≡ (as \\ us) ++ (bs \\ vs)
disjoint-diff {as} {bs} {us} {vs} d1 d2                     =  begin
   (as ++ bs) \\ (us ++ vs)                                 ≡⟨  ++-\\ {as} {bs} {us ++  vs} ⟩
   (as \\ (us ++ vs)) ++ (bs \\ (us ++ vs))                 ≡⟨ cong (λ k → k ++ (bs \\ (us ++ vs))) (sym (\\-++ {as}) ) ⟩
   ((as \\ us) \\ vs) ++ (bs \\ (us ++ vs))                 ≡⟨ cong (λ k → k ++ (bs \\ (us ++ vs)))  (\\-\\ {as} {us} {vs }) ⟩  
   ((as \\ vs) \\ us) ++ (bs \\ (us ++ vs))                 ≡⟨ cong (λ k →  (k \\ us) ++ (bs \\ (us ++ vs))  )  ( disjoint-lemma {as} {vs} d1) ⟩
   ( as  \\ us) ++ (bs \\ (us ++ vs))                       ≡⟨ cong (λ k → (as \\ us) ++ k)  (sym (\\-++ {bs})) ⟩
   ( as  \\ us) ++ ((bs \\ us) \\ vs)                       ≡⟨ cong (λ k → (as \\ us) ++ ( k \\ vs))  (disjoint-lemma {bs} {us} d2)  ⟩
   ( as  \\ us) ++ (bs  \\ vs)                              ∎

record Partition-< (split-at : ℕ) (list : List ℕ) : Set  where
   constructor parts
   field
      matched : List ℕ
      unmatched : List ℕ
      disjoint-proof : Disjoint matched unmatched
      filter-left : matched ≡  filter (λ k → k <? split-at) list
      filter-right : unmatched ≡ filter (λ k → ¬? (k <? split-at) )  list


notin-filter : ∀ {n} {P : Pred ℕ 0ℓ} → (P? : Decidable P) → (xs : List ℕ) → ¬ (P n) → n ∉ₙ filter P? xs
notin-filter {n} P? [] ¬Pn = notin-nil n
notin-filter {n} P? (x ∷ xs) ¬Pn with P? x
... | no _  = notin-filter P? xs ¬Pn
... | yes px = notin-cons (λ n≡x → ¬Pn (subst _ (sym n≡x) px)) (notin-filter P? xs ¬Pn)

pred-disjoint : ∀ {l l₁ l₂} → {P : Pred ℕ Level.zero} → (P? : Decidable P) → (l₁ ≡ filter P? l) → (l₂ ≡ filter (∁? P?) l) → Disjoint l₁ l₂
pred-disjoint {l} P? refl refl = disjoint proof₁ proof₂
  where
    proof₁ : ∀ n → ¬(n ∉ₙ filter P? l) → n ∉ₙ filter (∁? P?) l
    proof₁ n nin with P? n
    ... | yes pn = notin-filter (∁? P?) l (λ ¬pn → ¬pn pn)
    ... | no ¬pn = ⊥-elim (nin (notin-filter P? l ¬pn))

    proof₂ : ∀ n → ¬(n ∉ₙ filter (∁? P?) l) → n ∉ₙ filter P? l
    proof₂ n nin with P? n
    ... | no ¬pn = notin-filter P? l ¬pn
    ... | yes pn = ⊥-elim (nin (notin-filter (∁? P?) l (λ ¬pn → ¬pn pn)))

n-partition :  (n : ℕ)  →  (l : List ℕ) → Partition-< n l
n-partition  n  l with (partition (λ k → k <? n) l) | partition-defn  (λ k → k <? n) l 
... | fst , snd | pd = parts fst snd (pred-disjoint {l} {fst} {snd} (λ k → k <? n) (cong proj₁ pd) (cong proj₂ pd))   (cong proj₁ pd) (cong proj₂ pd)

