{-# OPTIONS --cubical-compatible --sized-types --guardedness #-}


module Bisimilarity where

open import Agda.Primitive
open import Agda.Builtin.Equality
open import Agda.Builtin.Size

open import InteractionTree

private variable
        a b c ℓ : Level
        i : Size

module _ {A B : Set c} {E : Set a → Set b} (r : A → B → Set) where
  mutual
    data euttF (sim : ITree i E A → ITree i E B → Set ) : ITree i E A → ITree i E B → Set (lsuc(a ⊔  b ⊔ c)) where
      EqRet  : ∀(a) → ∀(b) → (Rel : r a b) → euttF sim (Ret a) (Ret b)
--      EqVis  : ∀{R} → (e : E R) → ∀(k1) → ∀(k2)  → (Rel : ∀(v) → sim (tree (k1 v)) (tree (k2 v))) → euttF sim (Vis e k1) (Vis e k2)
--      EqTau  : ∀(t1) → ∀(t2) → (Rel : sim t1 t2) → euttF sim (Tau (itree t1)) (Tau (itree t2))
--      EqTauL : ∀(t1) → ∀(ot2) → (Rel : euttF sim t1 ot2) → euttF sim (Tau (itree t1)) ot2
--      EqTauR : ∀(ot1) → ∀(t2) → (Rel : euttF sim ot1 t2) → euttF sim ot1 (Tau (itree t2))

    record ∞euttF (sim : ITree i E A → ITree i E B → Set) (t1 : ITree i E A) (t2 : ITree i E B) : Set (lsuc(a ⊔  b ⊔ c)) where
      inductive
      field
        euttForce : ∀{t1 t2} → euttF sim t1 t2


  -- ≗ : (t₁ : ITree i E A) (t₂ : ITree i E B) → Set 
  -- ≗ (Ret t) (Ret x₁) = r t x₁
  -- ≗ (Ret x) (Tau x₁) = {!!}
  -- ≗ (Ret x) (Vis x₁ x₂) = {!!}
  -- ≗ (Tau x) t₂ = {!!}
  -- ≗ (Vis x x₁) t₂ = {!!}

  -- eutt : ITree i E A → ITree i E B → Set (lsuc(a ⊔  b ⊔ c))
  -- eutt = ∞euttF ≗
  
  -- Strong bisimulation, Leibniz equality for ITrees
--   infix 4 _≅_
  -- _≅_ : ITree i E A → ITree i E A → Set (lsuc(a ⊔  b ⊔ c))
  -- x ≅ y = ∀(P : ITree E A → Set (a ⊔  b ⊔ c)) → P x → P y

