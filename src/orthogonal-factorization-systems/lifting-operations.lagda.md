# Lifting operations

```agda
module orthogonal-factorization-systems.lifting-operations where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.functions
open import foundation.homotopies
open import foundation.sections
open import foundation.universe-levels

open import orthogonal-factorization-systems.pullback-hom
```

</details>

## Idea

Given two maps, `f : A → X` and `g : B → Y`, a _lifting operation between `f`
and `g`_ is a choice of lifting square for every commuting square

```text
  A ------> B
  |         |
 f|         |g
  |         |
  V         V
  X ------> Y.
```

Given a lifting operation we can say that `f` has a _left lifting structure_
with respect to `g` and that `g` has a _right lifting structure_ with respect to
`f`.

## Warning

This is the Curry–Howard interpretation of what is classically called _lifting
properties_. However, these are generally additional structure on the maps.

For the proof-irrelevant notion see
[`mere lifting properties`](orthogonal-factorization-systems.mere-lifting-properties.md).

## Definition

We define lifting operations to be sections of the pullback-hom.

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → X) (g : B → Y)
  where

  diagonal-lift : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  diagonal-lift = sec (pullback-hom f g)

  _⧄_ = diagonal-lift -- This symbol doesn't have an input sequence :(

  map-diagonal-lift : diagonal-lift → type-pullback-hom f g → X → B
  map-diagonal-lift = pr1

  issec-map-diagonal-lift :
    (d : diagonal-lift) → (pullback-hom f g ∘ map-diagonal-lift d) ~ id
  issec-map-diagonal-lift = pr2
```
