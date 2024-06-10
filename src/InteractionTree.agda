{-# OPTIONS --cubical-compatible  --sized-types --guardedness #-}

module InteractionTree where

open import Agda.Primitive
open import Agda.Builtin.Nat
open import Agda.Builtin.Size

open import Function.Base using (_∘_)

open import Effect.Functor
open import Effect.Applicative
open import Effect.Monad

mutual
  data ITree {a b c : Level} (i : Size) (E : Set a → Set b) (R : Set c) : Set (lsuc (a ⊔ b ⊔ c)) where
    Ret : R → ITree i E R
    Tau : ∞ITree i E R → ITree i E R
    Vis : ∀{A} → E A → (A → ∞ITree i E R) → ITree i E R

  record ∞ITree {a b c : Level} (i : Size) (E : Set a → Set b) (R : Set c) : Set (lsuc (a ⊔ b ⊔ c)) where
    constructor itree
    coinductive
    field
      tree : {j : Size< i} → ITree j E R

open ∞ITree public


private variable a b c ℓ : Level
private variable E : Set a → Set b
private variable R A B C : Set c
private variable i : Size
private variable j : Size< i

module Bind where
  mutual
    _>>=_ : ITree i E A → (A → ITree i E B) → ITree i E B
    Ret r    >>= f = f r
    Tau t    >>= f = Tau (t ∞>>= f) 
    Vis e k  >>= f = Vis e (λ x → (k x) ∞>>= f)

    _∞>>=_ :  ∞ITree i E A → (A → ITree i E B) → ∞ITree i E B
    tree (t ∞>>= f) = (tree t) >>= f
open Bind public

return : A → ITree i E A
return x = Ret x

_>>_ : ITree i E A → ITree i E B → ITree i E B
k >> m = k >>= λ _ → m

trigger : E R → ITree i E R
trigger e = Vis e λ x → f x where
  f : R → ∞ITree i E R
  tree (f x) = Ret x

∞trigger : E R → ∞ITree i E R
tree (∞trigger e) = Vis e λ x → f x where 
  f : R → ∞ITree i E R
  tree (f x) = Ret x

cat : (k : A → ITree i E B) → (h : B → ITree i E C) → A → ITree i E C
cat k h x = (k x) >>= h

-- burn : (n : Nat) → (t : ∞ITree i E R) → ∞ITree i E R
-- tree (burn n t) = burn' n (tree t)
--      where
--        burn' : (n : Nat) → ITree i E R → ITree i E R
--        burn' zero t = t
--        burn' (suc n) (Ret r)   = Ret r
--        burn' (suc n) (Tau t)   = tree (burn n t)
--        burn' (suc n) (Vis e k) = Vis e k
       
-- Functor, Applicative and Monad which are all defined by the monad operations.
open RawFunctor
ITreeFunctor : RawFunctor {ℓ} (ITree i E)
(ITreeFunctor <$> f) t = t >>= (return ∘ f)

open RawApplicative
ITreeApplicative : RawApplicative {ℓ} (ITree i E)
rawFunctor ITreeApplicative = ITreeFunctor
pure ITreeApplicative = return
(ITreeApplicative <*> f) t = f >>= (λ f' → t >>= λ t' → return (f' t'))

open RawMonad
ITreeMonad : RawMonad {ℓ} (ITree i E)
ITreeMonad = record {
  rawApplicative = ITreeApplicative
  ; _>>=_ = Bind._>>=_
  }
