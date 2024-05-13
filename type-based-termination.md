AIM XXXVIII, 13-18 May 2024 Swansea UK

Type-based termination: Sized types behind the veal
===================================================


Syntax-based termination is non-compositional
---------------------------------------------

__Example 1:__ Mapping over __rose trees__.

    data Rose (A : Set) : Set where
      rose : List (Rose A) → Rose A

    mapList : (A → B) → List A → List B

    mapRose : (A → B) → Rose A → Rose B
    mapRose f (rose rs) = rose (mapList (mapRose f) rs)

Traditional `--syntax-based-termination` cannot certify that `mapRose` is recursively applied to smaller arguments.
We have `rs < rose rs` but `mapRose` is only (directly) applied to `f` which stays the same.


The type system can fill in the missing communication.

    {-# OPTIONS --sized-types #-}

    data Rose (i : Size) (A : Set) : Set where
      rose : (j : Size< i) → List (Rose j A) → Rose i A

    mapList : (A → B) → List A → List B

    mapRose : (i : Size) → (A → B) → Rose i A → Rose i B
    mapRose i f (rose j rs) = rose j (mapList {A = Rose j A} (mapRose j f) rs)

Since `j < i`, call `mapRose j` is ok.


__Example 2: Decidable languages__ over alphabet `A`.

    record Lang : Set where
      field
        ν : Bool
        δ : A → Lang

Tries `Lang` memoize functions `List A → Bool` (Altenkirch 2001, Hinze 2000).
`Lang` is the terminal `Bool × (A → _)` coalgebra.
(An automaton `S → Bool × (A → S)` being just a coalgebra.)

Basic language constructors:

    ∅ : Lang
    ∅ .ν   = false
    ∅ .δ a = ∅

    ε : Lang
    ε .ν   = true
    ε .δ a = ∅

    chr : (A → Bool) → Lang
    chr p .ν   = false
    chr p .δ a = if p a then ε else ∅

Language union:

    _∪_ : Lang → Lang → Lang
    (k ∪ l) .ν   = k .ν or l .ν
    (k ∪ l) .δ a = k .δ a ∪ l .δ a

The recursive call to `_∪_` is guarded by copattern `.δ`.

Language concatenation:

    applyWhen : Bool → (A → A) → A → A

    _∙_ : Lang → Lang → Lang
    (k ∙ l) .ν   = k .ν and l .ν
    (k . l) .δ a = applyWhen (k .ν) (l .δ a ∪_) (k .δ a ∙ l)

The function `applyWhen (k .ν) (l .δ a ∪_)` sits between the recursive call to `_∙_`
and the guarding copattern.
Is this function benign and how can we certify this.

Communicate observations through types:

    record Lang (i : Size) : Set where
      field
        ν : Bool
        δ : (j : Size< i) → A → Lang j

    _∪_ : Lang → Lang → Lang
    (k ∪ l) .ν   = k .ν or l .ν
    (k ∪ l) .δ a = k .δ a ∪ l .δ a
