module Russian where

open import Data.Nat.Binary
open import Data.Nat.Binary.Properties
import Relation.Binary.PropositionalEquality as Eq
open Eq
open Eq.≡-Reasoning using (begin_; step-≡-∣; step-≡-⟩; _∎)

_ : ℕᵇ
_ = 1+[2 1+[2 2[1+ zero ] ] ]


half : ℕᵇ → ℕᵇ
half zero = zero
half 2[1+ x ] = suc x --  function in Data.Nat.Binary
half 1+[2 x ] = x

data Even : ℕᵇ → Set where
  even₀ : Even zero
  even₂ : ∀ x → Even 2[1+ x ]

data Odd : ℕᵇ → Set where
  odd₁ : ∀ x → Odd 1+[2 x ]


evenx⇒double-halfx≡x : ∀ {x} → Even x → double (half x) ≡ x
evenx⇒double-halfx≡x {x} even₀ = refl
evenx⇒double-halfx≡x {x} (even₂ y)        = begin
  double (half x)                         ≡⟨⟩
  double (half 2[1+ y ])                  ≡⟨⟩ 
  double (suc y)                          ≡⟨ sym ( 2[1+_]-double-suc y ) ⟩ -- 2[1+_]-double-suc from Data.Nat.Binary.Properties 
  2[1+ y ]                                ≡⟨⟩
  x                                       ∎

oddx⇒suc[double-halfx]≡x : ∀ {x} → Odd x → suc (double (half x)) ≡ x
oddx⇒suc[double-halfx]≡x {x} (odd₁ y)     = begin
    suc (double (half x))                       ≡⟨⟩
    suc (double ( half 1+[2 y ]))               ≡⟨⟩
    suc (double y)                              ≡⟨ sym (1+[2_]-suc-double y) ⟩ -- 1+[2_]-suc-double from Data.Nat.Binary.Properties
    1+[2 y ]                                    ≡⟨⟩
    x                                           ∎

evenx⇒halfx*doubley≡x*y : ∀ {x y} → Even x → (half x) * (double y) ≡ x * y
evenx⇒halfx*doubley≡x*y {x} {y} evenx      =  begin
    (half x) * (double y)                  ≡⟨ cong (λ k → (half x) * k) ( double[x]≡x+x y ) ⟩ -- double[x]≡x+x from Data.Nat.Binary.Properties
    (half x) * (y + y)                     ≡⟨ *-distribˡ-+ (half x) y y ⟩
    (half x) * y + (half x) * y            ≡⟨ sym ( double[x]≡x+x ((half x) * y) ) ⟩
    double ((half x) * y)                  ≡⟨  sym (double-*-assoc (half x) y)  ⟩
    double (half x) * y                    ≡⟨ cong (λ k → k * y) ( evenx⇒double-halfx≡x {x} evenx ) ⟩
    x * y                                  ∎


oddx⇒halfx*doubley+y≡x*y : ∀ {x y} → Odd x → (half x) * (double y) + y ≡ x * y
oddx⇒halfx*doubley+y≡x*y  {x} {y} oddx       = begin
   (half x) * (double y) + y                 ≡⟨ cong (λ k → (half x) * k + y)  ( double[x]≡x+x y) ⟩
   (half x) * (y + y) + y                    ≡⟨ cong (λ k → k + y) ( *-distribˡ-+ (half x) y y) ⟩
   (half x) * y + (half x) * y + y           ≡⟨ cong (λ k → k + y )  (sym ( double[x]≡x+x ((half x) * y))) ⟩
   double((half x) * y) + y                  ≡⟨ cong (λ k → k + y) ( sym ( double-*-assoc (half x) y)) ⟩
   double (half x) * y + y                   ≡⟨ +-comm (double (half x) * y)  y ⟩
   y + double (half x) * y                   ≡⟨ cong (λ k → y + k ) (*-comm (double (half x)) y) ⟩
   y + y * double (half x)                   ≡⟨ sym (*-suc y (double (half x))) ⟩
   y * (suc (double (half x)))               ≡⟨ *-comm y (suc (double (half x))) ⟩
   (suc (double (half x))) * y               ≡⟨ cong (λ k → k * y) ( oddx⇒suc[double-halfx]≡x {x} oddx ) ⟩
    x * y                                    ∎



data RussianPeasant : ℕᵇ → ℕᵇ → ℕᵇ →  Set where
    rp₀  : ∀ {b} → RussianPeasant zero b zero
    rpeven : ∀ {a b c} →
             Even a   →
             RussianPeasant (half a) (double b) c →
             RussianPeasant a b c
    rpodd  : ∀ {a b c c'} →
             Odd a →
             RussianPeasant (half a) (double b) c' →
             c ≡ c' + b →
             RussianPeasant a b c


russianPeasantAlgo-correct : ∀ {a b c} → RussianPeasant a b c → a * b ≡ c
russianPeasantAlgo-correct  rp₀   = refl
russianPeasantAlgo-correct  (rpeven {a} {b} {c} evenₐ rpa)    =  begin
     a * b                                                   ≡⟨ sym  (evenx⇒halfx*doubley≡x*y {a} {b} evenₐ) ⟩
     (half a ) * (double b)                                  ≡⟨ russianPeasantAlgo-correct rpa   ⟩
     c                                                       ∎
russianPeasantAlgo-correct  (rpodd {a} {b} {c} {c'} oddₐ rpa c1eq) = begin
    a * b                                                         ≡⟨ sym (oddx⇒halfx*doubley+y≡x*y {a} {b} oddₐ) ⟩
    (half a) * (double b) + b                                     ≡⟨ cong (λ k → k + b) ( russianPeasantAlgo-correct rpa) ⟩
    c' + b                                                        ≡⟨ sym c1eq ⟩
    c                                                             ∎

