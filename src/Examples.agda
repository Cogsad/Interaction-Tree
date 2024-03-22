{-# OPTIONS --cubical-compatible --safe --guardedness #-}

module Examples where

open import InteractionTree 

open import Agda.Primitive

private variable a b c ℓ : Level
private variable E : Set a → Set b
private variable R A B : Set c

-- These are examples from the Interaction Tree paper, translated from Coq to Agda

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

data ⊥ : Set where

record Unit : Set where
  instance constructor tt


data IO : Set → Set₁ where
  input : IO ℕ
  output : ℕ → IO Unit

echo : ∞ITree IO ⊥
tree echo = Vis input \n → itree(Vis(output n) \_ → echo)

spin : ∞ITree IO ⊥
tree spin = Tau spin

-- They used 9 here, but we use zero because of laziness. Shows the same functionality.
kill0 : ∞ITree IO Unit
tree kill0 = Vis input \{zero → itree(Ret tt) ; (suc _) → kill0}

-- These do not termination check! (Is there a way to fix this?)

-- echo2 : ITree IO ⊥
-- tree echo2 = (trigger' input) >>= λ x → (trigger' (output x)) >> (Tau echo2)

-- echo2 : ITree IO ⊥
-- tree echo2 = tree (trigger input) >>= λ x → (tree (trigger (output x))) >> (Tau echo2)

-- echo2 : ITree IO ⊥
-- tree echo2 = do
--              x ← tree (trigger input)
--              tree (trigger (output x))
--              Tau echo2
