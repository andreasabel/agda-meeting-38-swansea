{-# OPTIONS --type-based-termination #-}
{-# OPTIONS --no-syntax-based-termination #-}
{-# OPTIONS --size-preservation #-}  -- default

{-# OPTIONS -v term.tbt:50 #-}

data List A : Set where
  [] : List A
  _∷_ : A → List A → List A

data Rose (A : Set) : Set where
  rose : List (Rose A) → Rose A

module M (mapList : {A B : Set} → (A → B) → List A → List B) where
-- module M (mapList : {A B : Set} → (Rose A → Rose B) → List (Rose A) → List (Rose B)) where -- correctly fails

  mapRose : {A B : Set} → (A → B) → Rose A → Rose B
  mapRose f (rose rs) = rose (mapList (mapRose f) rs)
