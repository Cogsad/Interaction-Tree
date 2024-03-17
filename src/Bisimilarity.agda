{-# OPTIONS --guardedness #-}
{-# OPTIONS --large-indices #-}
module Bisimilarity where

open import Agda.Primitive

open import InteractionTree

private variable
        a b c ℓ : Level


module _ {A B : Set c} {E : Set a → Set b} (r : A → B → Set) where
  mutual
    data euttF (sim : ITree E A → ITree E B → Set c) : ITree E A → ITree E B → Set c where
      EqRet  : ∀(a) → ∀(b) → (Rel : r a b) → euttF sim (Ret a) (Ret b)
--      EqVis : ∀{R} → (e : E R) → ∀(k1) → ∀(k2)  → (Rel : ∀(v) → sim (k1 v) (k2 v)) → euttF sim (Vis e (itree k1)) (Vis e (itree k2))
      EqTau  : ∀(t1) → ∀(t2) → (Rel : sim t1 t2) → euttF sim (Tau (itree t1)) (Tau (itree t2))
      EqTauL : ∀(t1) → ∀(ot2) → (Rel : euttF sim t1 ot2) → euttF sim (Tau (itree t1)) ot2
      EqTauR : ∀(ot1) → ∀(t2) → (Rel : euttF sim ot1 t2) → euttF sim ot1 (Tau (itree t2))

    record ∞euttF (sim : ITree E A → ITree E B → Set c) (t1 : ITree E A) (t2 : ITree E B) : Set (lsuc a ⊔  b ⊔ c) where 
      inductive
      field
        euttForce : ∀{t1 t2} → euttF sim t1 t2

  -- _≅_ : ITree E A → ITree E B → Set c
  -- t1 ≅ t2 = euttF (λ _ _ → B) t1 t2


