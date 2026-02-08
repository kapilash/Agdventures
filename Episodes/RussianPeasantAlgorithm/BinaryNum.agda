module BinaryNum where

open import Data.Product
open import Data.Nat
open import Data.Nat.Properties
open import Data.Nat.Binary renaming (_*_ to _*ᵇ_; _+_ to _+ᵇ_; zero to zeroᵇ; suc to sucᵇ; pred to predᵇ)
open import Data.Nat.Binary.Properties hiding (+-comm)
open Data.Nat.Binary.Properties renaming (+-comm to +ᵇ-comm) public
open import Relation.Nullary.Negation
open import Data.Unit.Base using (⊤ ; tt)
open import Data.Empty using (⊥)
import Relation.Binary.PropositionalEquality as Eq
open Eq
open Eq.≡-Reasoning using (begin_; step-≡-∣; step-≡-⟩; _∎)
open import Function.Bundles


data Bin : Set where
  b′ : Bin
  _O : Bin → Bin
  _I : Bin → Bin

_ : Bin
_ = b′ I O I I

inc : Bin → Bin
inc b′ = b′ I
inc (x O) = x I
inc (x I) =   inc x O


_ : inc (b′ I O I I) ≡ (b′ I I O O)
_ = refl

_ : inc (b′ O O I O I I) ≡ (b′ O O I I O O )
_ = refl

doubleₙ : ℕ → ℕ
doubleₙ zero = zero
doubleₙ (suc n) = suc (suc (doubleₙ n) )

Bin→ℕ : Bin → ℕ
Bin→ℕ b′ = zero
Bin→ℕ (b O) = doubleₙ (Bin→ℕ b)
Bin→ℕ (b I) = suc (doubleₙ (Bin→ℕ b))

ℕ→Bin : ℕ → Bin
ℕ→Bin zero = b′
ℕ→Bin (suc x) = inc (ℕ→Bin x)

_ : ℕ→Bin (11) ≡ (b′ I O I I)
_ = refl

_ : Bin→ℕ (b′ I O I I) ≡ 11
_ = refl

_ : Bin→ℕ (b′ O O O I O I I) ≡ 11
_ = refl

_ : ℕ→Bin (Bin→ℕ (b′ I O I I)) ≡ (b′ I O I I)
_ = refl

doubleₙ-+ : ∀ n → doubleₙ n ≡ n + n
doubleₙ-+ zero = refl
doubleₙ-+ (suc n)              = begin
    doubleₙ  (suc n)           ≡⟨⟩
    suc (suc (doubleₙ n))    ≡⟨ cong (λ k → suc (suc k)) (doubleₙ-+ n) ⟩
    suc (suc (n + n))        ≡⟨⟩
    suc (suc n + n)          ≡⟨ cong suc  (+-comm (suc n) n) ⟩
    suc (n + suc n)          ≡⟨⟩
    suc n + (suc n)          ∎

doubleₙ-incr : ∀ n → doubleₙ (ℕ.suc n) ≡ ℕ.suc (ℕ.suc (doubleₙ n))
doubleₙ-incr n = refl

double-bin : Bin → Bin
double-bin b′ = b′
double-bin (b O) = b O O
double-bin (b I) = b I O



Bin+ : Bin → Bin → Bin
Bin+ b′ b2 = b2
Bin+ (b1 O) b′ = b1 O
Bin+ (b1 O) (b2 O) = double-bin  (Bin+ b1 b2)
Bin+ (b1 O) (b2 I) = inc (double-bin (Bin+ b1 b2))
Bin+ (b1 I) b′ = b1 I
Bin+ (b1 I) (b2 O) = inc (double-bin (Bin+ b1 b2))
Bin+ (b1 I) (b2 I) = inc (inc (double-bin (Bin+ b1 b2)))


double-bin-zero : double-bin b′ ≡ b′
double-bin-zero = refl

double-bin-inc : ∀ b → double-bin (inc b) ≡ inc (inc (double-bin b))
double-bin-inc b′ = refl
double-bin-inc (b O) = refl
double-bin-inc (b I) = refl

inc-double-bin : ∀ b → inc (double-bin b) ≡ b I
inc-double-bin b′ = refl
inc-double-bin (b O) = refl
inc-double-bin (b I) = refl

normalize : Bin → Bin
normalize b′ = b′
normalize (b O) with normalize b
... |  b′ =  b′
... |  foo = foo O
normalize (b I) with normalize b
... | b′ = b′ I
... | foo = foo I

HasI : Bin → Set
HasI b′ = ⊥
HasI (b O) = HasI b
HasI (b I) = ⊤

HasI-inc-b : ∀ (b : Bin) → HasI (inc b)
HasI-inc-b b′ = tt
HasI-inc-b (b O) = tt
HasI-inc-b (b I) = HasI-inc-b b

data Normalized : Bin → Set where
   norm-b : Normalized b′
   norm-I : ∀ b → Normalized b → Normalized (b I)
   norm-O : ∀ b → Normalized b → HasI b → Normalized (b O)

cong-normalized : ∀ b1 b2 → b1 ≡ b2 → Normalized b1 ≡ Normalized b2
cong-normalized b1 b2 b1=b2 rewrite b1=b2 = refl

normalizedn⇒normalized-incb : ∀ (b : Bin) → Normalized b → Normalized (inc b)
normalizedn⇒normalized-incb b norm-b = norm-I b′ norm-b
normalizedn⇒normalized-incb b (norm-I b₁ norm) = norm-O (inc b₁) (normalizedn⇒normalized-incb b₁ norm) (HasI-inc-b b₁)
normalizedn⇒normalized-incb b (norm-O b₁ norm x) = norm-I b₁ norm

normalizedn⇒normalized-doubleb : ∀ (b : Bin) → Normalized b → Normalized (double-bin b)
normalizedn⇒normalized-doubleb b norm-b = norm-b
normalizedn⇒normalized-doubleb b (norm-I b₁ norm) = norm-O (b₁ I) (norm-I b₁ norm) tt
normalizedn⇒normalized-doubleb b (norm-O b₁ norm x) = norm-O (b₁ O) (norm-O b₁ norm x) x


normalized-even-has-I : ∀ b → Normalized (b O) → HasI b
normalized-even-has-I b (norm-O b₁ norm x) = x

normalize-spec : ∀ b → Normalized (normalize b)
normalize-spec b′ = norm-b
normalize-spec (b  O) with (normalize b) | normalize-spec b
... | b′ | bar = bar
... | foo O | bar = norm-O (foo O) bar (normalized-even-has-I foo bar)
... | foo I | bar = norm-O (foo I) bar tt
normalize-spec (b I) with (normalize b) | normalize-spec b
... | b′ | bar = norm-I b′ bar
... | foo O | bar = norm-I (foo O) bar
... | foo I | bar = norm-I (foo I) bar

db-inc-db-norm : ∀ b → Normalized b → double-bin (inc (double-bin b)) ≡ b I O
db-inc-db-norm b′ norm = refl
db-inc-db-norm (b O) norm = refl
db-inc-db-norm (b I) norm = refl

db-inc≡inc-inc-db : ∀ b → double-bin (inc b) ≡ inc (inc (double-bin b))
db-inc≡inc-inc-db b′ = refl
db-inc≡inc-inc-db (b O) = refl
db-inc≡inc-inc-db (b I) = refl

Bin→ℕᵇ : Bin → ℕᵇ
Bin→ℕᵇ b′ = zeroᵇ
Bin→ℕᵇ (b′ I) = 1+[2 zeroᵇ ]
Bin→ℕᵇ ((b O) I) = 1+[2 Bin→ℕᵇ (b O) ]
Bin→ℕᵇ ((b I) I) = 1+[2 Bin→ℕᵇ (b I) ]
Bin→ℕᵇ (b′ O) = zeroᵇ
Bin→ℕᵇ ((b O) O) = double (Bin→ℕᵇ (b O))
Bin→ℕᵇ ((b I) O) = 2[1+ double (Bin→ℕᵇ b) ]

ℕᵇ→Bin : ℕᵇ → Bin
ℕᵇ→Bin zeroᵇ = b′
ℕᵇ→Bin 2[1+ n ] = double-bin (inc (ℕᵇ→Bin n))
ℕᵇ→Bin 1+[2 n ] = inc (double-bin (ℕᵇ→Bin n))

suffix-O≡double : ∀ b → Bin→ℕᵇ (b O) ≡ double (Bin→ℕᵇ b)
suffix-O≡double b′ = refl
suffix-O≡double (b O) = refl
suffix-O≡double (b′ I) = refl
suffix-O≡double ((b O) I) = refl
suffix-O≡double ((b I) I) = refl

convert-inc≡sucᵇ-convert : ∀ b → Bin→ℕᵇ (inc b) ≡ sucᵇ (Bin→ℕᵇ b)
convert-inc≡sucᵇ-convert b′ = refl
convert-inc≡sucᵇ-convert (b′ O) = refl
convert-inc≡sucᵇ-convert ((b O) O) rewrite (1+[2_]-suc-double  (Bin→ℕᵇ (b O)))= refl
convert-inc≡sucᵇ-convert ((b I) O) rewrite convert-inc≡sucᵇ-convert (b O) | suffix-O≡double b = refl
convert-inc≡sucᵇ-convert (b′ I) = refl
convert-inc≡sucᵇ-convert ((b O) I) rewrite (sym (suffix-O≡double b)) = refl
convert-inc≡sucᵇ-convert ((b I) I) rewrite (convert-inc≡sucᵇ-convert (b I)) | 2[1+_]-double-suc (Bin→ℕᵇ (b I)) = refl

double-bin-convert-double-convert : ∀ b → Bin→ℕᵇ (double-bin b) ≡ double (Bin→ℕᵇ b)
double-bin-convert-double-convert b′ = refl
double-bin-convert-double-convert (b O) = refl
double-bin-convert-double-convert (b′ I) = refl
double-bin-convert-double-convert ((b O) I) = refl
double-bin-convert-double-convert ((b I) I) = refl


double-convert≡adouble-bin-convert : ∀ n → ℕᵇ→Bin (double n) ≡ double-bin (ℕᵇ→Bin n)
double-convert≡adouble-bin-convert zeroᵇ = refl
double-convert≡adouble-bin-convert 1+[2 n ] rewrite double-convert≡adouble-bin-convert n = refl
double-convert≡adouble-bin-convert 2[1+ n ] rewrite db-inc≡inc-inc-db (ℕᵇ→Bin n) = refl

roundtrip-normalized-b : ∀ b → Normalized b → ℕᵇ→Bin (Bin→ℕᵇ b) ≡ b
roundtrip-normalized-b b′ norm = refl
roundtrip-normalized-b (b′ O) (norm-O b norm ())
roundtrip-normalized-b ((b O) O) (norm-O b₁ norm x) rewrite double-convert≡adouble-bin-convert (Bin→ℕᵇ (b O)) | roundtrip-normalized-b (b O) norm = refl
roundtrip-normalized-b ((b I) O) (norm-O b₁ (norm-I b normb) x) = begin
    ℕᵇ→Bin (Bin→ℕᵇ ((b I) O))                                  ≡⟨⟩
    ℕᵇ→Bin (2[1+ double (Bin→ℕᵇ b)])                           ≡⟨⟩
    double-bin (inc (ℕᵇ→Bin (double (Bin→ℕᵇ b))) )            ≡⟨ cong (λ k → double-bin (inc k)) (double-convert≡adouble-bin-convert (Bin→ℕᵇ b)) ⟩
    double-bin (inc (double-bin (ℕᵇ→Bin   (Bin→ℕᵇ b)    )))   ≡⟨ cong (λ k → double-bin (inc (double-bin k))) (roundtrip-normalized-b b normb) ⟩
    double-bin (inc (double-bin b))                           ≡⟨ db-inc-db-norm b normb ⟩
    b I O                                                       ∎
roundtrip-normalized-b (b′ I) (norm-I b₁ norm) = refl
roundtrip-normalized-b ((b O) I) (norm-I b₁ norm) rewrite roundtrip-normalized-b (b O) norm = refl
roundtrip-normalized-b ((b I) I) (norm-I b₁ norm) rewrite roundtrip-normalized-b (b I) norm = refl

roundtrip-n : ∀ n → Bin→ℕᵇ (ℕᵇ→Bin n) ≡ n
roundtrip-n zeroᵇ = refl
roundtrip-n 2[1+ n ]                = begin
   Bin→ℕᵇ (double-bin (inc (ℕᵇ→Bin n))) ≡⟨ double-bin-convert-double-convert ((inc (ℕᵇ→Bin n))) ⟩
   double (Bin→ℕᵇ (inc (ℕᵇ→Bin n) ))    ≡⟨ cong double (convert-inc≡sucᵇ-convert (ℕᵇ→Bin n)) ⟩
   double (sucᵇ (Bin→ℕᵇ (ℕᵇ→Bin n)) )   ≡⟨ cong (λ k → double (sucᵇ k)) (roundtrip-n n) ⟩
   double (sucᵇ n )                     ≡⟨ sym (2[1+_]-double-suc n) ⟩
   2[1+ n ]                             ∎
roundtrip-n 1+[2 n ] rewrite convert-inc≡sucᵇ-convert (double-bin (ℕᵇ→Bin n)) | double-bin-convert-double-convert  (ℕᵇ→Bin n) | roundtrip-n n  | (1+[2_]-suc-double n) = refl


ℕᵇ→Bin-is-normalized : ∀ n → Normalized (ℕᵇ→Bin n)
ℕᵇ→Bin-is-normalized zeroᵇ = norm-b
ℕᵇ→Bin-is-normalized 2[1+ n ]  = normalizedn⇒normalized-doubleb (inc (ℕᵇ→Bin n))  (normalizedn⇒normalized-incb (ℕᵇ→Bin n) (ℕᵇ→Bin-is-normalized n))
ℕᵇ→Bin-is-normalized 1+[2 n ] = normalizedn⇒normalized-incb (double-bin (ℕᵇ→Bin n))  (normalizedn⇒normalized-doubleb (ℕᵇ→Bin n ) (ℕᵇ→Bin-is-normalized n))


HasI-unique : ∀ b → (h1 h2 : HasI b) → h1 ≡ h2
HasI-unique b′ () h2
HasI-unique (b O) h1 h2 = HasI-unique b h1 h2
HasI-unique (b I) tt tt = refl

normalized-unique : ∀ b → (n1 n2 : Normalized b) → n1 ≡ n2
normalized-unique b′ norm-b norm-b = refl
normalized-unique (b O) (norm-O .b n1 x1) (norm-O .b n2 x2) rewrite normalized-unique b n1 n2 | HasI-unique b x1 x2 = refl
normalized-unique (b I) (norm-I .b n1) (norm-I .b n2) rewrite normalized-unique b n1 n2 = refl

record CanonicalBin : Set where
   field
     b :  Bin
     nd : Normalized b

congcb : ∀ (b1 b2 : Bin) → (nb1 : Normalized b1) → ( nb2 : Normalized b2 ) → b1 ≡ b2 → record { b = b1; nd = nb1 } ≡ record { b = b2; nd = nb2}
congcb b1 .b1 nb1 nb2 refl rewrite normalized-unique b1 nb1 nb2 = refl

cb→ℕᵇ : CanonicalBin → ℕᵇ
cb→ℕᵇ record { b = b ; nd = normalized } = Bin→ℕᵇ b

ℕᵇ→cb : ℕᵇ → CanonicalBin
ℕᵇ→cb n = record { b = ℕᵇ→Bin n ; nd = ℕᵇ→Bin-is-normalized n }

cb-ℕᵇ-cb : ∀ c → ℕᵇ→cb (cb→ℕᵇ c) ≡ c
cb-ℕᵇ-cb c@(record { b = b ; nd = normalized }) = begin
  ℕᵇ→cb (cb→ℕᵇ c)                    ≡⟨⟩
  ℕᵇ→cb (Bin→ℕᵇ (CanonicalBin.b c))  ≡⟨ refl ⟩
  record { b = ℕᵇ→Bin (Bin→ℕᵇ b) ; nd = ℕᵇ→Bin-is-normalized (Bin→ℕᵇ b) } ≡⟨ congcb (ℕᵇ→Bin (Bin→ℕᵇ b)) b (ℕᵇ→Bin-is-normalized (Bin→ℕᵇ b))   normalized (roundtrip-normalized-b b normalized) ⟩
  record { b = b; nd =  normalized } ≡⟨⟩
  c                                                            ∎ 

ℕᵇ-cb-ℕᵇ : ∀ n → cb→ℕᵇ ( ℕᵇ→cb n) ≡ n
ℕᵇ-cb-ℕᵇ n = begin
  cb→ℕᵇ (ℕᵇ→cb n)     ≡⟨⟩
  cb→ℕᵇ (record { b = ℕᵇ→Bin n ; nd = ℕᵇ→Bin-is-normalized n }) ≡⟨⟩
  Bin→ℕᵇ ( ℕᵇ→Bin n )            ≡⟨ roundtrip-n n ⟩
  n                   ∎

CanonicalBin-ℕᵇ-isomorphism : CanonicalBin ↔ ℕᵇ
CanonicalBin-ℕᵇ-isomorphism = mk↔ₛ′ cb→ℕᵇ ℕᵇ→cb ℕᵇ-cb-ℕᵇ cb-ℕᵇ-cb

-- Example: Defining operations via the isomorphism
_+ᶜᵇ_ : CanonicalBin → CanonicalBin → CanonicalBin
c1 +ᶜᵇ c2 = ℕᵇ→cb (cb→ℕᵇ c1 +ᵇ cb→ℕᵇ c2)

_*ᶜᵇ_ : CanonicalBin → CanonicalBin → CanonicalBin
c1 *ᶜᵇ c2 = ℕᵇ→cb (cb→ℕᵇ c1 *ᵇ cb→ℕᵇ c2)

-- Example: Transporting commutativity from ℕᵇ to CanonicalBin
-- The standard library has: +ᵇ-comm : ∀ m n → m +ᵇ n ≡ n +ᵇ m
+ᶜᵇ-comm : ∀ (c1 c2 : CanonicalBin) → c1 +ᶜᵇ c2 ≡ c2 +ᶜᵇ c1
+ᶜᵇ-comm c1 c2 = begin
  c1 +ᶜᵇ c2                           ≡⟨⟩
  ℕᵇ→cb (cb→ℕᵇ c1 +ᵇ cb→ℕᵇ c2)       ≡⟨ cong ℕᵇ→cb (+ᵇ-comm (cb→ℕᵇ c1) (cb→ℕᵇ c2)) ⟩
  ℕᵇ→cb (cb→ℕᵇ c2 +ᵇ cb→ℕᵇ c1)       ≡⟨⟩
  c2 +ᶜᵇ c1                           ∎ 
