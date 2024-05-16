
{-# OPTIONS --cubical-compatible --safe --guardedness #-}

module InteractionTree where

open import Agda.Primitive
open import Agda.Builtin.Nat

open import Function.Base using (_∘_)

open import Effect.Functor
open import Effect.Applicative
open import Effect.Monad

mutual
  data ITree {a b c : Level} (E : Set a → Set b) (R : Set c) : Set (lsuc (a ⊔ b ⊔ c)) where
    Ret : R → ITree E R
    Tau : ∞ITree E R → ITree E R
    Vis : ∀{A} → E A → (A → ∞ITree E R) → ITree E R

  record ∞ITree {a b c : Level} (E : Set a → Set b) (R : Set c) : Set (lsuc (a ⊔ b ⊔ c)) where
    constructor itree
    coinductive
    field
      tree : ITree E R

open ∞ITree public


private variable a b c ℓ : Level
private variable E : Set a → Set b
private variable R A B C : Set c

module Bind where
  mutual
    _>>=_ : ITree E A → (A → ITree E B) → ITree E B
    Ret r    >>= f = f r
    Tau t    >>= f = Tau (t ∞>>= f)
    Vis e k  >>= f = Vis e λ x → (k x) ∞>>= f

    _∞>>=_ : ∞ITree E A → (A → ITree E B) → ∞ITree E B
    tree (t ∞>>= f) = (tree t) >>= f
open Bind public

return : A → ITree E A
return x = Ret x


_>>_ : ITree E A → ITree E B → ITree E B
k >> m = k >>= λ _ → m
trigger : E R → ITree E R
trigger e = Vis e λ x → itree (Ret x)

∞trigger : E R → ∞ITree E R
tree (∞trigger e) = Vis e (λ x → itree (Ret x))

cat : (k : A → ITree E B) → (h : B → ITree E C) → A → ITree E C
cat k h x = (k x) >>= h

burn : (n : Nat) → (t : ∞ITree E R) → ∞ITree E R
tree (burn n t) = burn' n (tree t)
     where
       burn' : (n : Nat) → ITree E R → ITree E R
       burn' zero t = t
       burn' (suc n) (Ret r)   = Ret r
       burn' (suc n) (Tau t)   = tree (burn n t)
       burn' (suc n) (Vis e k) = Vis e k
       
-- Functor, Applicative and Monad which are all defined by the monad operations.
open RawFunctor
ITreeFunctor : RawFunctor {ℓ} (ITree E)
(ITreeFunctor <$> f) t = t >>= (return ∘ f)

open RawApplicative
ITreeApplicative : RawApplicative {ℓ} (ITree E)
rawFunctor ITreeApplicative = ITreeFunctor
pure ITreeApplicative = return
(ITreeApplicative <*> f) t = f >>= (λ f' → t >>= λ t' → return (f' t'))

open RawMonad
ITreeMonad : RawMonad {ℓ} (ITree E)
ITreeMonad = record {
  rawApplicative = ITreeApplicative
  ; _>>=_ = Bind._>>=_
  }
