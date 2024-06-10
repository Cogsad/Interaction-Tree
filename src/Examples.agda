{-# OPTIONS --cubical-compatible --sized-types --guardedness #-}

module Examples where

open import InteractionTree 

open import Agda.Primitive
open import Agda.Builtin.Size

private variable a b c ℓ : Level
private variable E : Set a → Set b
private variable R A B : Set c
private variable i : Size


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

echo : ∞ITree i IO ⊥
tree echo = Vis input f where
  f : ℕ → ∞ITree i IO ⊥
  tree (f n) = Vis (output n) \_ → echo

spin : ∞ITree i IO ⊥
tree spin = Tau spin

-- They used 9 here, but we use zero because of laziness. Shows the same functionality.
kill0 : ∞ITree i IO Unit
tree kill0 = Vis input f where
  f : ℕ → ∞ITree i IO Unit
  tree (f zero) = Ret tt
  f (suc n) = kill0


echo2 : ∞ITree i IO ⊥
tree echo2 = (trigger input) >>= λ x → (trigger (output x)) >> (Tau echo2)

echo2' : ∞ITree i IO ⊥
tree echo2' = tree (∞trigger input) >>= λ x → (tree (∞trigger (output x))) >> (Tau echo2)

echo2'' : ∞ITree i IO ⊥
tree echo2'' = do
               x ← (trigger input)
               (trigger (output x))
               Tau echo2
