
{-# OPTIONS --type-based-termination #-}
{-# OPTIONS --no-syntax-based-termination #-}
{-# OPTIONS --size-preservation #-} -- default

{-# OPTIONS -v term.tbt:50 #-}

open import Agda.Builtin.Sigma

_×_ : (A B : Set) → Set  -- ∀[]. ∀E. ∀E. ⁺∞
A × B = Σ A λ _ → B

record Stream (A : Set) : Set where    -- ∀[∞]. ∀E. ⁻t₀<+ε₀>
                                       -- ∀ i A → Stream -i +A

  coinductive                          -- ∀[∞]. ∀E. ⁺∞<*⁺∞, *⁺∞, *ε₀, +⁺∞ → ⁻t₀<+ε₀>> → ⁻t₀<+ε₀>
                                       -- ∀ i A → (Σ A λ _ → Stream -i +A) → Stream -i +A
  field
    force : A × Stream A               -- ∀[<1, ∞]. ∀E. ⁻t₁<+ε₀> → ⁺∞<*⁺∞, *⁺∞, *ε₀, +⁺∞ → ⁻t₀<+ε₀>>
                                       -- ∀[i'<i, i] A → Stream -i +A → Σ A λ _ → Stream -i' +A
open Stream

module _ (A B : Set) where

  mutual

    record SP : Set where          -- ∀[∞]. ∀E. ∀E. ⁻t₀<-ε₁, +ε₀>
                                   -- ∀ i A B → SP -i -A +B

      coinductive                  -- ∀[∞, ∞]. ∀E. ∀E. (⁺t₀,⁻t₁)<-ε₁, +ε₀> → ⁻t₁<-ε₁, +ε₀>
                                   -- ∀[j, i] A B → SP' +j -i -A +B → SP -i -A +B

      field force : SP'            -- ∀[<1, ∞, ∞]. ∀E. ∀E. ⁻t₁<-ε₁, +ε₀> → (⁺t₂,⁻t₀)<-ε₁, +ε₀>
                                   -- ∀[i' < i, i, j] A B → SP -i -A +B → SP' +j -i' -A +B

    data SP' : Set where           -- ∀[∞]. ∀E. ∀E. (⁺t₀,⁻t₁)<-ε₁, +ε₀>    JUST ONE QUANTIFIER?
                                   -- ∀ j A B → SP' +j -i -A +B

      get : (A → SP') → SP'        -- ∀[<2, ∞, ∞]. ∀E. ∀E. (ε₁ → (⁺t₀,⁻t₁)<-ε₁, +ε₀>) → (⁺t₂,⁻t₁)<-ε₁, +ε₀>
                                   -- ∀[j'<j, i, j] A B → (A → SP' +j' -i -A + B) → SP' +j -i -A +B

      put : B → SP → SP'           -- ∀[∞, ∞]. ∀E. ∀E. ε₀ → ⁻t₀<-ε₁, +ε₀> → (⁺t₁,⁻t₀)<-ε₁, +ε₀>
                                   -- ∀[j, i] A B → B → SP -i -A +B → SP' +j -i -A +B

  open SP

  mutual
    eval : SP → Stream A → Stream B          -- ∀[∞]. ∀E. ∀E. ⁺∞<-ε₁, +ε₀> → ⁺∞<+ε₁, +ε₀, +ε₁> → ⁻t₀<+ε₁, +ε₀, +ε₀>
    eval sp s .force = eval' (sp .force) s

    eval' : SP' → Stream A → B × Stream B    -- ∀[∞, ∞]. ∀E. ∀E. ⁺t₀<-ε₁, +ε₀> → ⁺∞<+ε₁, +ε₀, +ε₁> → ⁺∞<*⁺∞, *⁺∞, *ε₀, +⁺∞ → ⁻t₁<+ε₁, +ε₀, +ε₀>>
    eval' (put b sp) s = b , eval sp s
    eval' (get f)    s =
      let  a , as = s .force
      in   eval' (f a) as

-- -}
-- -}
-- -}
-- -}
