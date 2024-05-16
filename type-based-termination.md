AIM XXXVIII, 13-18 May 2024 Swansea UK

Type-based termination: Sized types behind the veil
===================================================


Type-based termination is compositional
---------------------------------------

__Example 1:__ Mapping over __rose trees__.

    data Rose (A : Set) : Set where
      rose : A → List (Rose A) → Rose A

    mapList : (A → B) → List A → List B

    mapRose : (A → B) → Rose A → Rose B
    mapRose f (rose a rs) = rose (f a) (mapList {A = Rose A} (mapRose f) rs)

Traditional `--syntax-based-termination` cannot certify that `mapRose` is recursively applied to smaller arguments.
We have `rs < rose rs` but `mapRose` is only (directly) applied to `f` which stays the same.


The type system can fill in the missing communication.

    {-# OPTIONS --sized-types #-}

    data Rose (i : Size) (A : Set) : Set where
      rose : (j : Size< i) → A → List (Rose j A) → Rose i A

    mapList : (A → B) → List A → List B

    mapRose : (i : Size) → (A → B) → Rose i A → Rose i B
    mapRose i f (rose j a rs) = rose j (f a) (mapList {A = Rose j A} (mapRose j f) rs)

Since `j < i`, call `mapRose j` is ok.


__Example 2: Decidable languages__ over alphabet `A`.

    record Lang : Set where
      coinductive
      field
        ν : Bool
        δ : A → Lang

Tries `Lang` memoize functions `List A → Bool` (Altenkirch 2001, Hinze 2000).
`Lang` is the terminal `Bool × (A → _)` coalgebra.
(An automaton `S → Bool × (A → S)` being just _a_ coalgebra.)

l .δ a = { w | aw ∈ l }

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

    union : Lang → Lang → Lang
    union k l .ν   = or    (k .ν)   (l .ν)
    union k l .δ a = union (k .δ a) (l .δ a)

The recursive call to `union` is guarded by copattern `.δ`.

Language concatenation:

    applyWhen : Bool → (A → A) → A → A

    concat : Lang → Lang → Lang
    concat k l .ν   = and (k .ν) (l .ν)
    concat k l .δ a = applyWhen (k .ν) (union (l .δ a)) (concat (k .δ a) l)

The function `applyWhen (k .ν) (union (l .δ a))` sits between the recursive call to `concat`
and the guarding copattern.
Ok? Why?

Communicate observations through types:

    record Lang (i : Size) : Set where
      coinduction
      field
        ν : Bool
        δ : (j : Size< i) → A → Lang j

    union : (i : Size) → Lang i → Lang i → Lang i
    union i k l .ν     = or      (k .ν)     (l .ν)
    union i k l .δ j a = union j (k .δ j a) (l .δ j a)

Since `j < i`, the call `union j` is ok.
Further `union k l` is at least as deeply defined as `k` and `l` are.
`union` is "size-preserving".

    applyWhen : Bool → (A → A) → A → A

    concat : (i : Size) → Lang i → Lang i → Lang i
    concat i k l .ν     = and (k .ν) (l .ν)
    concat i k l .δ j a =
      applyWhen {A = Lang j} (k .ν) (union j (l .δ j a)) (concat j (k .δ j a) l)

Since `j < i`, the call `concat j` is ok.
Also `l : Lang i` implies `l : Lang j` by subsumption, so
`concat j (k .δ j a) l) : Lang j`.


Type-based termination PR
-------------------------

Kanstantsin Nisht implemented a shadow sized type system
that gives type-based termination without explicit size annotations from the user.

https://github.com/agda/agda/pull/7152



Assigning sizes to data
-----------------------

In a mixed mutual block,

- size parameter `i` of coinductive types is dominant
- inductive types carry through `i` and get their own subordinary parameter `j`

```agda

    {-# OPTIONS --type-based-termination #-}

    record SP : Set where          -- SP (@- i : Size)
      coinductive
      field force : SP'            -- (i' : Size< i) → SP i → SP' i' j

    data SP' : Set where           --  SP' (@- i) (@+ j)
      get : (A → SP') → SP'        --  (j' : Size< j) → (A → SP' i j') → SP' i j
      put : B → SP → SP'           --  (j' : Size< j) → B → SP i → SP' i j

```

Example: interpreting SP as Stream transducers:

```agda

  mutual
    eval : SP → Stream A → Stream B
    eval sp s .force = eval' (sp .force) s

    eval' : SP' → Stream A → B × Stream B
    eval' (put b sp) s = b , eval sp s
    eval' (get f)    s =
      let  a , as = s .force
      in   eval' (f a) as

```

Assigning sizes to function types
---------------------------------

- size variables for the negative occurrences (co(induction))
- `∞` for positive occurrences (just parameters)

```agda

    eval  : SP → Stream A → Stream B        -- SP ∞    → Stream ∞ A → Stream i B
    eval' : SP' → Stream A → B × Stream B   -- SP' ∞ j → Stream ∞ A → B × Stream i B

```

Assigning sizes to patterns
---------------------------

LHSs generate rigid size variables:

```agda

    eval : SP ∞ → Stream ∞ A → Stream i B
    eval sp s .force                       -- eval i sp s .force i'  [i, i'<i]

    eval' : SP' ∞ j → Stream ∞ A → B × Stream i B
    eval' (put b sp) s                     -- eval' i j (put j' b sp) s  [i, j, j'<j]
    eval' (get f)    s                     -- eval' i j (get j' f)    s  [i, j, j'<j]

```

Assigning sizes to expressions
------------------------------

Insert flexible size variables, solve constraints.

```agda

i, i'<i     ⊢   eval' ?i ?j (sp .force ?k) s : B × Stream i' B   ↝  i' ≤ ?i, ?k < ∞+1

i, j, j'<j  ⊢   b , eval ?i sp s             : B × Stream i' B   ↝  i' ≤ ?i
i, j, j'<j  ⊢   let  a , as = s .force
                in   eval' ?i ?j (f a) as    : B × Stream i' B   ↝  i' ≤ ?i, j' ≤ ?j

```

Construct and analyse call-graph
--------------------------------

Same as existing size-change termination checker,
only that size-change comes from sizes.

    eval  --> eval'  |< .|

    eval' --> eval   |=|
                     |.|

    eval' --> eval'  |= .|   (idempotent)
                     |. <|

Derived

    eval  --> eval   |<|     (idempotent)

Each idempotent call matrix needs a `<` in the diagonal.
