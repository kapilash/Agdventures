{-# OPTIONS --safe #-}

open import Data.Empty using (⊥)
open import Data.Unit.Base using (⊤)
open import Relation.Binary using (Rel; IsEquivalence; Setoid; Decidable)
open import Level renaming (_⊔_ to _⊔ˡ_)
open import Algebra
open import Algebra.Lattice
open import Data.List
open import Data.Bool using (Bool; true; false; not)
open import Data.Product using (proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary.Decidable



record IsBoundedDistributiveLattice {a ℓ} {A : Set a} (_≈_ : Rel A ℓ) (_∨_ _∧_ : Op₂ A) (⊤ ⊥ : A) : Set (a ⊔ˡ ℓ) where
  field
    isDistributiveLattice : IsDistributiveLattice _≈_ _∨_ _∧_
    ∨-identity : Identity _≈_ ⊥ _∨_ 
    ∧-identity : Identity _≈_ ⊤ _∧_ 

record IsDeMorganAlgebra {a ℓ} {A : Set a}   (_≈_ : Rel A ℓ) (_∨_ _∧_ : Op₂ A) (⊤ ⊥ : A) (-_ : A → A) : Set (a ⊔ˡ ℓ) where
  field
    isBoundedDistributiveLattice : IsBoundedDistributiveLattice _≈_ _∨_ _∧_ ⊤ ⊥

    involution : ∀ x → (- (- x)) ≈ x

    neg-top : (- ⊤) ≈ ⊥
    neg-bottom : (- ⊥) ≈ ⊤

    neg-∨-is-∧ : ∀ x y → (- (x ∨ y)) ≈ ((- x) ∧ (- y))
    neg-∧-is-∨ : ∀ x y → (- (x ∧ y)) ≈ ((- x) ∨ (- y))

    neg-cong : ∀ {x y} → x ≈ y → (- x) ≈ (- y)


record IsDecDeMorganAlgebra {a ℓ} {A : Set a} (_≈_ : Rel A ℓ) (_∨_ _∧_ : Op₂ A) (⊤ ⊥ : A) (-_ : A → A) : Set (a ⊔ˡ ℓ) where
  field
    isDeMorganAlgebra : IsDeMorganAlgebra _≈_ _∨_ _∧_ ⊤ ⊥ -_
    _≟_               : Decidable _≈_


join-monoid : ∀ {a ℓ} {A : Set a} {_≈_ : Rel A ℓ} {_∨_ _∧_ : Op₂ A} {⊤ ⊥ : A}
            → IsBoundedDistributiveLattice _≈_ _∨_ _∧_ ⊤ ⊥
            → IsMonoid _≈_ _∨_ ⊥
join-monoid isBDL = record
  { isSemigroup = record
      { isMagma = record
          { isEquivalence = isEquivalence
          ; ∙-cong        = ∨-cong
          }
      ; assoc = ∨-assoc
      }
  ; identity = ∨-identity
  }
  where
    open IsBoundedDistributiveLattice isBDL
      using (isDistributiveLattice; ∨-identity; ∧-identity)
    open IsDistributiveLattice isDistributiveLattice
      using (isLattice)
    open IsLattice isLattice
      using (isEquivalence; ∨-cong; ∨-assoc; ∧-cong; ∧-assoc)


meet-monoid : ∀ {a ℓ} {A : Set a} {_≈_ : Rel A ℓ} {_∨_ _∧_ : Op₂ A} {⊤ ⊥ : A}
            → IsBoundedDistributiveLattice _≈_ _∨_ _∧_ ⊤ ⊥
            → IsMonoid _≈_ _∧_ ⊤
meet-monoid isBDL = record
  { isSemigroup = record
      { isMagma = record
          { isEquivalence = isEquivalence
          ; ∙-cong        = ∧-cong
          }
      ; assoc = ∧-assoc
      }
  ; identity = ∧-identity
  }
  where
    open IsBoundedDistributiveLattice isBDL
      using (isDistributiveLattice; ∨-identity; ∧-identity)
    open IsDistributiveLattice isDistributiveLattice
      using (isLattice)
    open IsLattice isLattice
      using (isEquivalence; ∨-cong; ∨-assoc; ∧-cong; ∧-assoc)

data GameTree {a} (A : Set a) : Set a where
    Leaf : A → GameTree A
    Node : List (GameTree A) → GameTree A


   

module GT {a ℓ} {A : Set a} {_≈_ : Rel A ℓ}
          {_∨_ _∧_ : Op₂ A} {⊤ ⊥ : A} { -_ : A → A}
          (iddma : IsDecDeMorganAlgebra _≈_ _∨_ _∧_ ⊤ ⊥ -_) where

  open IsDecDeMorganAlgebra iddma public
       using (_≟_)
  open IsDeMorganAlgebra (IsDecDeMorganAlgebra.isDeMorganAlgebra iddma) public
  open IsBoundedDistributiveLattice isBoundedDistributiveLattice public
       using (isDistributiveLattice; ∨-identity; ∧-identity)
  open IsDistributiveLattice isDistributiveLattice public
       using (isLattice; ∧-distribˡ-∨)
  open IsLattice isLattice public
       using (isEquivalence; ∨-cong; ∧-cong; ∨-comm; ∧-comm; ∨-assoc; ∧-assoc; absorptive)
  open IsEquivalence isEquivalence public
       renaming (refl to ≈-refl; sym to ≈-sym; trans to ≈-trans)

  private
    setoid : Setoid a ℓ
    setoid = record { isEquivalence = isEquivalence }

  open import Relation.Binary.Reasoning.Setoid setoid


  -- Min-max evaluation.
  mutual
    maxmin : GameTree A → A
    maxmin (Leaf v)  = v
    maxmin (Node ts) = maxs ts

    minmax : GameTree A → A
    minmax (Leaf v)  = v
    minmax (Node ts) = mins ts

    maxs : List (GameTree A) → A
    maxs []       = ⊥
    maxs (t ∷ ts) = minmax t ∨ maxs ts

    mins : List (GameTree A) → A
    mins []       = ⊤
    mins (t ∷ ts) = maxmin t ∧ mins ts

  -- Sign-flipping leaves at alternating depths.
  -- The flag b says whether the *current* root sits at a min level.
  mutual
    negate : Bool → GameTree A → GameTree A
    negate false (Leaf x)  = Leaf x
    negate true  (Leaf x)  = Leaf (- x)
    negate b     (Node ts) = Node (neglist (not b) ts)

    neglist : Bool → List (GameTree A) → List (GameTree A)
    neglist _ []       = []
    neglist b (t ∷ ts) = negate b t ∷ neglist b ts

  -- Negamax evaluation.
  mutual
    negamax : GameTree A → A
    negamax (Leaf x)  = x
    negamax (Node ts) = negmaxs ts

    negmaxs : List (GameTree A) → A
    negmaxs []       = ⊥
    negmaxs (t ∷ ts) = (- negamax t) ∨ negmaxs ts

  -- Equivalence of min-max and negamax.
  mutual
    maxmin-negamax : ∀ (t : GameTree A) → maxmin t ≈ negamax (negate false t)
    maxmin-negamax (Leaf x)  = ≈-refl
    maxmin-negamax (Node ts) = maxs-negmaxs ts

    minmax-negamax : ∀ (t : GameTree A) → minmax t ≈ (- negamax (negate true t))
    minmax-negamax (Leaf x)  = ≈-sym (involution x)
    minmax-negamax (Node ts) = mins-negmaxs ts

    maxs-negmaxs : ∀ (ts : List (GameTree A)) → maxs ts ≈ negmaxs (neglist true ts)
    maxs-negmaxs []       = ≈-refl
    maxs-negmaxs (t ∷ ts) = ∨-cong (minmax-negamax t) (maxs-negmaxs ts)

    mins-negmaxs : ∀ (ts : List (GameTree A)) → mins ts ≈ (- negmaxs (neglist false ts))
    mins-negmaxs []       = ≈-sym neg-bottom
    mins-negmaxs (t ∷ ts) =
      begin
        maxmin t ∧ mins ts
      ≈⟨ ∧-cong (maxmin-negamax t) (mins-negmaxs ts) ⟩
        negamax (negate false t) ∧ (- negmaxs (neglist false ts))
      ≈⟨ ∧-cong (≈-sym (involution _)) ≈-refl ⟩
        (- (- negamax (negate false t))) ∧ (- negmaxs (neglist false ts))
      ≈⟨ ≈-sym (neg-∨-is-∧ _ _) ⟩
        - ((- negamax (negate false t)) ∨ negmaxs (neglist false ts))
      ∎

  -- Fail-hard alpha-beta: leaves are clamped to the window [a, b].
  mutual
    αβ-negmax : A → A → GameTree A → A
    αβ-negmax a b (Leaf x)      = a ∨ (x ∧ b)
    αβ-negmax a b (Node forest) = αβ-negmaxs a b forest

    αβ-negmaxs : A → A → List (GameTree A) → A
    αβ-negmaxs a _ [] = a
    αβ-negmaxs a b (tree ∷ forest) with (a ∨ (- (αβ-negmax (- b) (- a) tree)))
    ... | a' with a' ≟ (a' ∨ b)
    ... | no _  = αβ-negmaxs a' b forest
    ... | yes _ = a'

  -- A few derived lattice facts used in the spec proof.
  private
    ∨-identityˡ : ∀ x → (⊥ ∨ x) ≈ x
    ∨-identityˡ x = proj₁ ∨-identity x

    ∨-identityʳ : ∀ x → (x ∨ ⊥) ≈ x
    ∨-identityʳ x = proj₂ ∨-identity x

    ∧-identityʳ : ∀ x → (x ∧ ⊤) ≈ x
    ∧-identityʳ x = proj₂ ∧-identity x

    ∨-absorbs-∧ : ∀ x y → (x ∨ (x ∧ y)) ≈ x
    ∨-absorbs-∧ = proj₁ absorptive

    ∧-absorbs-∨ : ∀ x y → (x ∧ (x ∨ y)) ≈ x
    ∧-absorbs-∨ = proj₂ absorptive

    ∧-zeroˡ : ∀ x → (⊥ ∧ x) ≈ ⊥
    ∧-zeroˡ x = begin
      ⊥ ∧ x         ≈⟨ ∧-cong ≈-refl (≈-sym (∨-identityˡ x)) ⟩
      ⊥ ∧ (⊥ ∨ x)   ≈⟨ ∧-absorbs-∨ ⊥ x ⟩
      ⊥             ∎

    ≡⇒≈ : ∀ {x y : A} → x ≡ y → x ≈ y
    ≡⇒≈ refl = ≈-refl

  -- Spec: αβ with bounds [a, b] returns the negamax value clamped to [a, b].
  -- The clamp on Leaf makes the spec hold uniformly.
  mutual
    αβ-spec : ∀ a b t → αβ-negmax a b t ≈ (a ∨ (negamax t ∧ b))
    αβ-spec a b (Leaf x)      = ≈-refl
    αβ-spec a b (Node forest) = αβs-spec a b forest

    αβs-spec : ∀ a b forest → αβ-negmaxs a b forest ≈ (a ∨ (negmaxs forest ∧ b))
    αβs-spec a b [] = ≈-sym (≈-trans (∨-cong ≈-refl (∧-zeroˡ b)) (∨-identityʳ a))
    αβs-spec a b (tree ∷ forest)
      with a ∨ (- αβ-negmax (- b) (- a) tree) in a'-eq
    ... | a' with a' ≟ (a' ∨ b)
    ...   | yes p = begin
            a'
              ≈⟨ p ⟩
            a' ∨ b
              ≈⟨ ∨-cong ≈-refl (≈-sym (∨-absorbs-∧ b (negmaxs forest))) ⟩
            a' ∨ (b ∨ (b ∧ negmaxs forest))
              ≈⟨ ≈-sym (∨-assoc a' b (b ∧ negmaxs forest)) ⟩
            (a' ∨ b) ∨ (b ∧ negmaxs forest)
              ≈⟨ ∨-cong (≈-sym p) ≈-refl ⟩
            a' ∨ (b ∧ negmaxs forest)
              ≈⟨ ∨-cong (≈-trans (≈-sym (≡⇒≈ a'-eq)) (helper-a' a b tree)) ≈-refl ⟩
            (a ∨ (b ∧ (- negamax tree))) ∨ (b ∧ negmaxs forest)
              ≈⟨ ∨-assoc a (b ∧ (- negamax tree)) (b ∧ negmaxs forest) ⟩
            a ∨ ((b ∧ (- negamax tree)) ∨ (b ∧ negmaxs forest))
              ≈⟨ ∨-cong ≈-refl (≈-sym (∧-distribˡ-∨ b (- negamax tree) (negmaxs forest))) ⟩
            a ∨ (b ∧ ((- negamax tree) ∨ negmaxs forest))
              ≈⟨ ∨-cong ≈-refl (∧-comm b ((- negamax tree) ∨ negmaxs forest)) ⟩
            a ∨ (((- negamax tree) ∨ negmaxs forest) ∧ b)
              ∎
    ...   | no _ = begin
            αβ-negmaxs a' b forest
              ≈⟨ αβs-spec a' b forest ⟩
            a' ∨ (negmaxs forest ∧ b)
              ≈⟨ ∨-cong ≈-refl (∧-comm (negmaxs forest) b) ⟩
            a' ∨ (b ∧ negmaxs forest)
              ≈⟨ ∨-cong (≈-trans (≈-sym (≡⇒≈ a'-eq)) (helper-a' a b tree)) ≈-refl ⟩
            (a ∨ (b ∧ (- negamax tree))) ∨ (b ∧ negmaxs forest)
              ≈⟨ ∨-assoc a (b ∧ (- negamax tree)) (b ∧ negmaxs forest) ⟩
            a ∨ ((b ∧ (- negamax tree)) ∨ (b ∧ negmaxs forest))
              ≈⟨ ∨-cong ≈-refl (≈-sym (∧-distribˡ-∨ b (- negamax tree) (negmaxs forest))) ⟩
            a ∨ (b ∧ ((- negamax tree) ∨ negmaxs forest))
              ≈⟨ ∨-cong ≈-refl (∧-comm b ((- negamax tree) ∨ negmaxs forest)) ⟩
            a ∨ (((- negamax tree) ∨ negmaxs forest) ∧ b)
              ∎

    -- Pull the inner αβ-negmax through the spec, then DeMorgan + involution + distrib.
    helper-a' : ∀ a b tree
              → (a ∨ (- αβ-negmax (- b) (- a) tree)) ≈ (a ∨ (b ∧ (- negamax tree)))
    helper-a' a b tree = begin
      a ∨ (- αβ-negmax (- b) (- a) tree)
        ≈⟨ ∨-cong ≈-refl (neg-cong (αβ-spec (- b) (- a) tree)) ⟩
      a ∨ (- ((- b) ∨ (negamax tree ∧ (- a))))
        ≈⟨ ∨-cong ≈-refl (neg-∨-is-∧ (- b) (negamax tree ∧ (- a))) ⟩
      a ∨ ((- (- b)) ∧ (- (negamax tree ∧ (- a))))
        ≈⟨ ∨-cong ≈-refl (∧-cong (involution b) ≈-refl) ⟩
      a ∨ (b ∧ (- (negamax tree ∧ (- a))))
        ≈⟨ ∨-cong ≈-refl (∧-cong ≈-refl (neg-∧-is-∨ (negamax tree) (- a))) ⟩
      a ∨ (b ∧ ((- negamax tree) ∨ (- (- a))))
        ≈⟨ ∨-cong ≈-refl (∧-cong ≈-refl (∨-cong ≈-refl (involution a))) ⟩
      a ∨ (b ∧ ((- negamax tree) ∨ a))
        ≈⟨ ∨-cong ≈-refl (∧-distribˡ-∨ b (- negamax tree) a) ⟩
      a ∨ ((b ∧ (- negamax tree)) ∨ (b ∧ a))
        ≈⟨ ∨-cong ≈-refl (∨-comm (b ∧ (- negamax tree)) (b ∧ a)) ⟩
      a ∨ ((b ∧ a) ∨ (b ∧ (- negamax tree)))
        ≈⟨ ≈-sym (∨-assoc a (b ∧ a) (b ∧ (- negamax tree))) ⟩
      (a ∨ (b ∧ a)) ∨ (b ∧ (- negamax tree))
        ≈⟨ ∨-cong (≈-trans (∨-cong ≈-refl (∧-comm b a)) (∨-absorbs-∧ a b)) ≈-refl ⟩
      a ∨ (b ∧ (- negamax tree))
        ∎

  αβ-negamax-extremes : ∀ tree → αβ-negmax ⊥ ⊤ tree ≈ negamax tree
  αβ-negamax-extremes tree = begin
    αβ-negmax ⊥ ⊤ tree
      ≈⟨ αβ-spec ⊥ ⊤ tree ⟩
    ⊥ ∨ (negamax tree ∧ ⊤)
      ≈⟨ ∨-cong ≈-refl (∧-identityʳ (negamax tree)) ⟩
    ⊥ ∨ negamax tree
      ≈⟨ ∨-identityˡ (negamax tree) ⟩
    negamax tree
      ∎

  -- Empty window: bounds collapse, so αβ returns the lower bound regardless of the tree.
  αβ-negmax-pinned : ∀ a t → αβ-negmax a a t ≈ a
  αβ-negmax-pinned a t = begin
    αβ-negmax a a t
      ≈⟨ αβ-spec a a t ⟩
    a ∨ (negamax t ∧ a)
      ≈⟨ ∨-cong ≈-refl (∧-comm (negamax t) a) ⟩
    a ∨ (a ∧ negamax t)
      ≈⟨ proj₁ absorptive a (negamax t) ⟩
    a
      ∎

  αβ-negamaxs-extremes : ∀ forest → αβ-negmaxs ⊥ ⊤ forest ≈ negmaxs forest
  αβ-negamaxs-extremes forest = begin
    αβ-negmaxs ⊥ ⊤ forest
      ≈⟨ αβs-spec ⊥ ⊤ forest ⟩
    ⊥ ∨ (negmaxs forest ∧ ⊤)
      ≈⟨ ∨-cong ≈-refl (∧-identityʳ (negmaxs forest)) ⟩
    ⊥ ∨ negmaxs forest
      ≈⟨ ∨-identityˡ (negmaxs forest) ⟩
    negmaxs forest
      ∎
