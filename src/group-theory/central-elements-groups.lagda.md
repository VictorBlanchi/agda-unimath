# Central elements of groups

```agda
module group-theory.central-elements-groups where
```

<details><summary>Imports</summary>

```agda
open import foundation.identity-types
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels

open import group-theory.central-elements-monoids
open import group-theory.conjugation
open import group-theory.groups
```

</details>

## Idea

An element `x` of a group `G` is said to be central if `xy ＝ yx` for every
`y : G`.

## Definition

```agda
module _
  {l : Level} (G : Group l)
  where

  is-central-element-group-Prop : type-Group G → Prop l
  is-central-element-group-Prop =
    is-central-element-monoid-Prop (monoid-Group G)

  is-central-element-Group : type-Group G → UU l
  is-central-element-Group = is-central-element-Monoid (monoid-Group G)

  is-prop-is-central-element-Group :
    (x : type-Group G) → is-prop (is-central-element-Group x)
  is-prop-is-central-element-Group =
    is-prop-is-central-element-Monoid (monoid-Group G)
```

## Properties

### The unit element is central

```agda
module _
  {l : Level} (G : Group l)
  where

  is-central-element-unit-Group : is-central-element-Group G (unit-Group G)
  is-central-element-unit-Group =
    is-central-element-unit-Monoid (monoid-Group G)
```

### The product of two central elements is central

```agda
module _
  {l : Level} (G : Group l)
  where

  is-central-element-mul-Group :
    (x y : type-Group G) →
    is-central-element-Group G x → is-central-element-Group G y →
    is-central-element-Group G (mul-Group G x y)
  is-central-element-mul-Group =
    is-central-element-mul-Monoid (monoid-Group G)
```

### The inverse of a central element is central

```agda
module _
  {l : Level} (G : Group l)
  where

  is-central-element-inv-Group :
    (x : type-Group G) → is-central-element-Group G x →
    is-central-element-Group G (inv-Group G x)
  is-central-element-inv-Group x H y =
    ( inv (inv-left-div-Group G y x)) ∙
    ( ( ap (inv-Group G) (inv (H (inv-Group G y)))) ∙
      ( inv-right-div-Group G x y))
```

### The central elements are closed under conjugation

```agda
module _
  {l : Level} (G : Group l)
  where

  is-fixed-point-conjugation-is-central-element-Group :
    (x y : type-Group G) → is-central-element-Group G x →
    conjugation-Group G y x ＝ x
  is-fixed-point-conjugation-is-central-element-Group x y H =
    ( ap (mul-Group' G (inv-Group G y)) (inv (H y))) ∙
    ( isretr-mul-inv-Group' G y x)

  is-central-element-conjugation-Group :
    (x y : type-Group G) → is-central-element-Group G x →
    is-central-element-Group G (conjugation-Group G y x)
  is-central-element-conjugation-Group x y H =
    is-closed-under-eq-subtype'
      ( is-central-element-group-Prop G)
      ( H)
      ( is-fixed-point-conjugation-is-central-element-Group x y H)
```
