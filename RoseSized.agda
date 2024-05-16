{-# OPTIONS --sized-types #-}

open import Agda.Builtin.List
open import Agda.Builtin.Size

data Rose (i : Size) (A : Set) : Set where
  rose : (j : Size< i) → A → List (Rose j A) → Rose i A

module _ (mapList : ∀ {A B} → (A → B) → List A → List B) where

    mapRose : ∀ {A B} (i : Size) → (A → B) → Rose i A → Rose i B
    mapRose {A} i f (rose j a rs) = rose j (f a) (mapList {A = Rose j A} (mapRose j f) rs)

-- -}
