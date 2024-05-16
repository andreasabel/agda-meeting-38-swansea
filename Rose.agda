{-# OPTIONS --type-based-termination #-}
{-# OPTIONS --no-syntax-based-termination #-}
{-# OPTIONS --size-preservation #-}  -- default

{-# OPTIONS -v term.tbt:50 #-}


variable
  A B : Set

module PostulatedList where

  {-# POLARITY List ++ #-}

  postulate
    List : Set → Set
    mapList : (A → B) → List A → List B

module DefinedList where

  data List A : Set where                  -- ∀[∞]. ∀E. ⁺t₀<+ε₀>
    [] : List A                            -- ∀E. ⁺t₀<+ε₀>
    _∷_ : A → List A → List A              -- ∀[<1, ∞]. ∀E. ε₀ → ⁺t₀<+ε₀> → ⁺t₁<+ε₀>

  mapList : (A → B) → List A → List B      -- ∀[∞]. ∀E. ∀E. (ε₁ → ε₀) → ⁺t₀<+ε₁> → ⁺∞<+ε₀>
  mapList f [] = []
  mapList f (x ∷ xs) = f x ∷ mapList f xs
  --
  -- Preservation candidates:  SizeDecomposition {sdPositive = [1], sdNegative = [0], sdOther = []}
  -- original sig:             ∀[∞, ∞]. ∀E. ∀E. (ε₁ → ε₀) → ⁺t₀<+ε₁> → ⁺t₁<+ε₀>
  -- Encoded function mapList, sized type:
  --                           ∀[∞]. ∀E. ∀E. (ε₁ → ε₀) → ⁺t₀<+ε₁> → ⁺∞<+ε₀>
  -- Signature of mapList after size-preservation inference:
  --                           ∀[∞]. ∀E. ∀E. (ε₁ → ε₀) → ⁺t₀<+ε₁> → ⁺t₀<+ε₀>

-- open PostulatedList  -- does not work
open DefinedList -- works

data Rose (A : Set) : Set where      -- ∀[∞]. ∀E. ⁺t₀<+ε₀>
  rose : A → List (Rose A) → Rose A      -- ∀[<1, ∞]. ∀E. ⁺∞<+⁺t₀<+ε₀>> → ⁺t₁<+ε₀>

mapRose : (A → B) → Rose A → Rose B  -- ∀[∞]. ∀E. ∀E. (ε₁ → ε₀) → ⁺t₀<+ε₁> → ⁺∞<+ε₀>
mapRose f (rose a rs) = rose (f a) (mapList (mapRose f) rs)

  -- Signature of mapRose after size-preservation inference:
  -- ∀[∞]. ∀E. ∀E. (ε₁ → ε₀) → ⁺t₀<+ε₁> → ⁺t₀<+ε₀>
