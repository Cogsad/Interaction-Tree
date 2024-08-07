{-# OPTIONS  --sized-types --guardedness #-}

module Bisimilarity where

open import Agda.Primitive
open import Agda.Builtin.Size

open import InteractionTree

private variable
        a b c ℓ : Level


module EuttF (A B : Set c) (E : Set a → Set b) (r : A → A → Set (lsuc c)) where
  mutual
    data euttF {i : Size} (sim : ∞ITree ∞ E A → ∞ITree ∞ E A → Set) : ITree ∞ E A → ITree ∞ E A → Set (lsuc(a ⊔  b ⊔ c)) where
      EqRet  : ∀(a) → ∀(b) → (Rel : r a b) → euttF sim  (Ret a) (Ret b)
      EqVis  : ∀{R} → (e : E R) → ∀(k1) → ∀(k2)  → (Rel : ∀(v) → sim ((k1 v)) ((k2 v))) → euttF sim (Vis e k1) (Vis e k2)
      EqTau  : ∀(t1) → ∀(t2) → (Rel : sim t1 t2) → euttF sim (Tau  t1) (Tau t2)

      -- Weak bisimular relations
      -- EqTauL : ∀(t1) → ∀(ot2) → (Rel : ∞euttF i sim t1 ot2) → euttF sim t1 ot2
      -- EqTauR : ∀(ot1) → ∀(t2) → (Rel : ∞euttF i sim ot1 t2) → euttF sim ot1 t2



    record ∞euttF i (sim : ∞ITree ∞ E A → ∞ITree ∞ E A → Set) (t1 : ITree ∞ E A) (t2 : ITree ∞ E A) : Set (lsuc(a ⊔  b ⊔ c)) where
      coinductive
      field
        euttForce : {j : Size< i} → euttF sim  t1 t2


-- Strong bisimulation
module _ {A B : Set c} {E : Set a → Set b} where
  _≐_ : ∀ (x y : A) → Set (lsuc c)
  _≐_  x y = ∀ (P : A → Set c) → P x → P y

  refl-≐ :{x : A} →  x ≐ x
  refl-≐ x Px = Px

  sym-≐ : ∀ {x y : A} → x ≐ y → y ≐ x
  sym-≐ {x} {y}  x≐y P Py = Qy Py where
    Q : A → Set c
    Q z = P z → P x
    Qx : Q x
    Qx = refl-≐ P
    Qy : Q y
    Qy = x≐y Q Qx

  trans-≐ : ∀ {x y z : A} → x ≐ y → y ≐ z → x ≐ z
  trans-≐ x≐y y≐z  P px = y≐z P (x≐y P px)

  open EuttF A B E (_≐_) public

  reflexive : ∀{i sim} t (f : (t₁ : ∞ITree ∞ E A) →  (t₂ : ∞ITree ∞ E A) → sim t₁ t₂) → euttF {i} sim t t
  reflexive (Ret r) f = EqRet r r refl-≐
  reflexive (Tau t) f = EqTau t t (f t t)
  reflexive (Vis e k) f = EqVis e k k λ v → f (k v) (k v)

  symmetric : ∀{i sim} t t' (f : (t₁ : ∞ITree ∞ E A) →  (t₂ : ∞ITree ∞ E A) → sim t₁ t₂) → euttF {i} sim t t' → euttF sim t' t
  symmetric .(Ret a) .(Ret b) _ (EuttF.EqRet a b Rel) = EqRet b a (sym-≐ Rel)
  symmetric .(Vis e k1) .(Vis e k2) f (EuttF.EqVis {R} e k1 k2 Rel) = EqVis e k2 k1 λ v → f (k2 v) (k1 v)
  symmetric .(Tau t1) .(Tau t2) f (EuttF.EqTau  t1 t2 Rel) = EqTau t2 t1 (f t2 t1)

  transitive : ∀{i sim} t₁ t₂ t₃ → (f : (t₁ : ∞ITree ∞ E A) →  (t₂ : ∞ITree ∞ E A) → sim t₁ t₂) → euttF {i} sim t₁ t₂ → euttF {i} sim t₂ t₃ → euttF {i} sim t₁ t₃
  transitive .(Ret a) .(Ret b) .(Ret c) f (EuttF.EqRet a b Rel) (EuttF.EqRet .b c Rel') = EqRet a c (trans-≐ Rel Rel')
  transitive .(Vis e k1) .(Vis e k2) .(Vis e k3) f (EuttF.EqVis e k1 k2 Rel) (EuttF.EqVis .e .k2 k3 Rel') = EqVis e k1 k3 λ v → f (k1 v) (k3 v)
  transitive .(Tau t1) .(Tau t2) .(Tau t3) f (EuttF.EqTau t1 t2 Rel) (EuttF.EqTau .t2 t3 Rel') = EqTau t1 t3 (f t1 t3)
