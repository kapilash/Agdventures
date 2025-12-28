module Miu where

open import Data.Product
open import Data.Nat
open import Data.Nat.Properties
open import Data.Nat.DivMod
open import Data.List using (List; []; _∷_; length; _++_; map; filter; foldr)
open import Data.List.Properties
open import Data.Sum
open import Relation.Nullary.Negation
open import Agda.Builtin.Nat
import Relation.Binary.PropositionalEquality as Eq
open Eq
open Eq.≡-Reasoning using (begin_; step-≡-∣; step-≡-⟩; _∎)

data Symbol : Set where
 M : Symbol
 I : Symbol
 U : Symbol

MiuString = List Symbol

data MiuSystem : MiuString → Set where
   axiom : MiuSystem (M ∷ I ∷  [])
   rule1 : ∀ {s} → MiuSystem (s ++ (I ∷ [])) → MiuSystem (s ++ (I ∷ U ∷ []))
   rule2 : ∀ {s} → MiuSystem (M ∷ s) → MiuSystem (M ∷ s ++ s)
   rule3 : ∀ {s t} → MiuSystem (s ++ I ∷ I ∷ I ∷ t) → MiuSystem (s ++ (U ∷ t))
   rule4 : ∀ {s t} → MiuSystem (s ++ U ∷ U ∷ t) → MiuSystem (s ++ t)



countI : MiuString → ℕ
countI [] = zero
countI (M ∷ str) = countI str
countI (I ∷ str) = suc (countI str)
countI (U ∷ str) = countI str








countI-++ : ∀ (s₁ s₂ : MiuString) → countI (s₁ ++ s₂) ≡ countI s₁ + countI s₂
countI-++ [] s₂ = refl
countI-++ (M ∷ s₁) s₂ = countI-++ s₁ s₂
countI-++ (I ∷ s₁) s₂ = cong suc (countI-++ s₁ s₂)
countI-++ (U ∷ s₁) s₂ = countI-++ s₁ s₂










data NotMultiple₃ : ℕ → Set where
  rem₁ : (k : ℕ) → ∃[ m ]( k ≡ 1 +  m * 3 ) → NotMultiple₃ k
  rem₂ : (k : ℕ) → ∃[ m ]( k ≡ 2 +  m * 3 ) → NotMultiple₃ k


not-multiple₃-1 : NotMultiple₃ 1
not-multiple₃-1 = rem₁ 1 (zero , refl)



not-multiple₃-2 : NotMultiple₃ 2
not-multiple₃-2 = rem₂ 2 (zero , refl)

not-multiple₃-cong : ∀ {n m : ℕ} → NotMultiple₃ n → n ≡ m → NotMultiple₃ m
not-multiple₃-cong {n} {m} (rem₁ n (fst , snd)) neqm = rem₁ m (fst , trans (sym neqm) snd)
not-multiple₃-cong {n} {m} (rem₂ n (fst , snd)) neqm = rem₂ m  (fst , trans (sym neqm) snd)




nmod3≡1⇒∃k : ∀ (n : ℕ) → (n % 3) ≡ 1 → ∃[ k ](n ≡ 1 + k * 3) 
nmod3≡1⇒∃k n eq = n  / 3 ,  helper 
  where
   helper : n ≡  1 + (n / 3) * 3
   helper                        = begin
      n                          ≡⟨ m≡m%n+[m/n]*n n 3 ⟩
      (n % 3) + (n / 3) * 3      ≡⟨ cong (λ x → x + (n / 3) * 3) eq ⟩
      1 + (n / 3) * 3            ∎

nmod3≡2⇒∃k : ∀ (n : ℕ) → (n % 3) ≡ 2 → ∃[ k ] (n ≡ 2 +  k * 3)
nmod3≡2⇒∃k n eq = (n / 3) , helper
   where
     helper : n ≡ 2 + (n / 3) * 3 
     helper                      = begin
      n                          ≡⟨ m≡m%n+[m/n]*n n 3 ⟩
      (n % 3) + (n / 3) * 3      ≡⟨ cong (λ x → x + (n / 3) * 3) eq ⟩
      2 + (n / 3) * 3            ∎

n%3≡1or2⇒NotMultiple₃ : ∀ (x : ℕ) → (x % 3) ≡ 1 ⊎ (x % 3) ≡ 2 → NotMultiple₃ x
n%3≡1or2⇒NotMultiple₃ x (inj₁ x₁) = rem₁ x ( nmod3≡1⇒∃k x x₁)
n%3≡1or2⇒NotMultiple₃ x (inj₂ y) = rem₂ x (nmod3≡2⇒∃k x y)

nm₃-x⇒x%3≡1or2 : ∀ (x : ℕ) → NotMultiple₃ x → (x % 3) ≡ 1 ⊎ (x % 3) ≡ 2
nm₃-x⇒x%3≡1or2 x (rem₁ x keq) = inj₁ (rem1-conv x keq)
  where rem1-conv : ∀ (k : ℕ) → ∃[ m ]( k ≡ 1 + m * 3 ) → k % 3 ≡ 1
        rem1-conv k (m , keq)          = begin
          k % 3                        ≡⟨ cong (λ x → x % 3) keq ⟩
          (1 + m * 3) % 3              ≡⟨  [m+kn]%n≡m%n 1 m 3  ⟩
          1                            ∎
nm₃-x⇒x%3≡1or2 x (rem₂ k keq) = inj₂ (rem2-conv x keq)
 where
   rem2-conv : ∀ (k : ℕ) → ∃[ m ]( k ≡ 2 + m * 3 ) → k % 3 ≡ 2
   rem2-conv k (m , keq)          = begin
     k % 3                        ≡⟨ cong (λ x → x % 3) keq ⟩
     (2 + m * 3) % 3              ≡⟨  [m+kn]%n≡m%n 2 m 3  ⟩
     2                            ∎

x+3%3≡x%3 : ∀ (x : ℕ) → (x + 3) % 3 ≡ x % 3
x+3%3≡x%3 zero = refl
x+3%3≡x%3 (suc zero) = refl
x+3%3≡x%3 (2+ zero) = refl
x+3%3≡x%3 (2+ (suc x)) = x+3%3≡x%3 x

x%3≡1or2⇒2x%3≡1or2 : ∀ (x : ℕ) → (x % 3) ≡ 1 ⊎ (x % 3) ≡ 2 → (2 * x) % 3 ≡ 1 ⊎ (2 * x) % 3 ≡ 2
x%3≡1or2⇒2x%3≡1or2 x (inj₁ x₁) =  inj₂ (helper1 x₁)
 where helper1 : (x % 3) ≡ 1 → (2 * x) % 3 ≡ 2
       helper1 xeq1                    = begin
         (2  * x) % 3                   ≡⟨ %-distribˡ-* 2 x 3  ⟩
         ((2 % 3) * (x % 3)) % 3        ≡⟨⟩
         (2 * (x % 3)) % 3              ≡⟨ cong (λ k → (2 * k) % 3 ) xeq1 ⟩
         2                             ∎
x%3≡1or2⇒2x%3≡1or2 x (inj₂ y) = inj₁ (helper2 y)
 where helper2 : (x % 3) ≡ 2 → (2 * x) % 3 ≡ 1
       helper2 xeq2                     = begin
         (2  * x) % 3                   ≡⟨   %-distribˡ-*  2 x 3 ⟩
         ((2 % 3) * (x % 3)) % 3        ≡⟨⟩
         (2 * (x % 3)) % 3              ≡⟨  cong (λ k → (2 * k) % 3) xeq2 ⟩
         1                              ∎

not-multiple₃-x⇒not-multiple₃-2x : ∀ {x : ℕ} → NotMultiple₃ x → NotMultiple₃ (2 * x)
not-multiple₃-x⇒not-multiple₃-2x {x} nm3x = n%3≡1or2⇒NotMultiple₃ (2 * x)  (x%3≡1or2⇒2x%3≡1or2 x ( nm₃-x⇒x%3≡1or2 x nm3x))


not-multiple₃-x+3⇒not-multiple₃-x : ∀ {x : ℕ} → NotMultiple₃ (x + 3) → NotMultiple₃ x
not-multiple₃-x+3⇒not-multiple₃-x {x} nm3 = helper (nm₃-x⇒x%3≡1or2 (x + 3) nm3)
   where
     helper1 : ∀ {n : ℕ} → (n + 3) % 3 ≡ 1 → NotMultiple₃ n
     helper1 {n} neq = n%3≡1or2⇒NotMultiple₃ n  (inj₁ ( trans ( sym (x+3%3≡x%3 n )) neq))

     helper2 : ∀ {n : ℕ} → (n + 3) % 3 ≡ 2 → NotMultiple₃ n
     helper2 {n} neq = n%3≡1or2⇒NotMultiple₃ n (inj₂ (trans (sym (x+3%3≡x%3 n)) neq))

     helper : ∀ {x : ℕ} → ((x + 3) % 3 ≡ 1 ⊎ (x + 3) % 3 ≡ 2)  → NotMultiple₃ x
     helper (inj₁ x) = helper1 x
     helper (inj₂ y) = helper2 y




lemma-rule1 : ∀ {s} → countI (s ++ I ∷ []) ≡ countI (s ++ I ∷ U ∷ [])
lemma-rule1 {s}                  = begin
  countI (s ++ I ∷ [])           ≡⟨ countI-++ s (I ∷ []) ⟩
  countI s + countI (I ∷ [])     ≡⟨⟩
  countI s + countI (I ∷ U ∷ []) ≡⟨ sym (countI-++ s (I ∷ U ∷ [])) ⟩
  countI (s  ++ I ∷ U ∷ [])      ∎


lemma-rule2 : ∀ {s} → countI (s ++ s) ≡ 2 * countI s
lemma-rule2 {s}                 = begin
  countI (s ++ s)               ≡⟨ countI-++ s s ⟩
  countI s + countI s           ≡⟨ cong (λ k → countI s + k) (sym (+-identityʳ (countI s))) ⟩
  countI s + (countI s + 0)     ≡⟨⟩
  2 * countI s                  ∎

lemma-rule3 : ∀ {s t} → countI (s ++ I ∷ I ∷ I ∷ t) ≡ countI (s ++ U ∷ t) + 3
lemma-rule3 {s} {t}                      = begin
  countI (s ++ I ∷ I ∷ I ∷ t)            ≡⟨ countI-++ s (I ∷ I ∷ I ∷ t) ⟩
  countI s + countI (I ∷ I ∷ I ∷ t)      ≡⟨⟩
  countI s + (3 + countI t)                ≡⟨ cong (λ k → countI s + k) (+-comm 3 (countI t)) ⟩
  countI s + (countI t + 3)              ≡⟨ sym (+-assoc (countI s) (countI t) 3)  ⟩
  (countI s + countI t) + 3              ≡⟨⟩
  (countI s + countI (U ∷ t)) + 3        ≡⟨ cong (λ k → k + 3) (sym (countI-++ s (U ∷ t))) ⟩

  countI (s ++ U ∷ t) + 3                ∎


lemma-rule4 : ∀ {s t} → countI (s ++ U ∷ U ∷ t) ≡ countI (s ++ t)
lemma-rule4 {s} {t}                 = begin
   countI (s ++ U ∷ U ∷ t)          ≡⟨ countI-++ s (U ∷ U ∷ t) ⟩
   countI s + countI (U ∷ U ∷ t)    ≡⟨⟩
   countI s + countI t              ≡⟨ sym (countI-++ s t) ⟩
   countI (s ++ t)                  ∎


miutheorem : ∀ {s} → MiuSystem s → NotMultiple₃ (countI s)
miutheorem {s} axiom = not-multiple₃-1
miutheorem {s} (rule1 {t} mius) = not-multiple₃-cong {countI (t ++ I ∷ [])} {countI (t ++ I ∷ U ∷ [])} (miutheorem mius) (lemma-rule1 {t})
miutheorem {s} (rule2 {t} mius) rewrite lemma-rule2 {t} = not-multiple₃-x⇒not-multiple₃-2x {(countI t)} (miutheorem mius)
miutheorem {s} (rule3 {t1} {t2} mius) = not-multiple₃-x+3⇒not-multiple₃-x {countI s} (not-multiple₃-cong {countI (t1 ++ I ∷ I ∷ I ∷ t2)} {countI (t1 ++ U ∷ t2) + 3} (miutheorem mius) (lemma-rule3 {t1} {t2}))
miutheorem {s} (rule4 {t1} {t2} mius) = not-multiple₃-cong {countI (t1 ++ U ∷ U ∷ t2)} {countI (t1 ++ t2)} (miutheorem mius) (lemma-rule4 {t1} {t2})


n≡0⇒multiple₃-0 : ∀ n → n ≡ 0 → ¬ NotMultiple₃ n
n≡0⇒multiple₃-0 zero neq (rem₁ k (fst , ()))
n≡0⇒multiple₃-0 (suc n) () (rem₁ k (fst , snd))
n≡0⇒multiple₃-0 zero neq (rem₂ k (fst , ()))
n≡0⇒multiple₃-0 (suc n) () (rem₂ k (fst , snd))


mu-puzzle : ¬ MiuSystem (M ∷ U ∷ [])
mu-puzzle x = n≡0⇒multiple₃-0 (countI (M ∷ U ∷ [])) refl (miutheorem x)
