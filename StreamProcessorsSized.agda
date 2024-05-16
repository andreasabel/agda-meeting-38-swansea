open import Agda.Builtin.Size
open import Agda.Builtin.Sigma

module _ (A B : Set) where

_×_ : (A B : Set) → Set
A × B = Σ A λ _ → B

mutual

  record SP (i : Size) : Set where
    coinductive
    field
      force : {i' : Size< i} → SP' i' ∞

  data SP' (i j : Size) : Set where
    get : {j' : Size< j} → (A → SP' i j') → SP' i j
    put : B → SP i → SP' i j

open SP

record Stream (i : Size) (A : Set) : Set where
  coinductive
  field
    force : {i' : Size< i} → A × Stream i' A
open Stream

variable
  i j : Size
  i' j' : Size< i

module SP∞ where

  mutual
    eval : SP ∞ → Stream ∞ A → Stream i B
    eval sp s .force = eval' (sp .force) s

    eval' : SP' ∞ j → Stream ∞ A → B × Stream i B
    eval' (get f)    s = let a , as = s .force in eval' (f a) as
    eval' (put b sp) s = b , eval sp s

mutual
  eval : SP i → Stream ∞ A → Stream i B
  eval sp s .force = eval' (sp .force) s

  eval' : {i' : Size< i} → SP' i' j → Stream ∞ A → B × Stream i' B
  eval' (get f)    s = let a , as = s .force in eval' (f a) as
  eval' (put b sp) s = b , eval sp s
