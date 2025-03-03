# Functoriality of propositional truncations

```agda
module foundation.functoriality-propositional-truncation where
```

<details><summary>Imports</summary>

```agda
open import foundation.propositional-truncations

open import foundation-core.contractible-types
open import foundation-core.dependent-pair-types
open import foundation-core.equivalences
open import foundation-core.function-extensionality
open import foundation-core.functions
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.propositions
open import foundation-core.universe-levels
```

</details>

## Idea

The universal property of propositional truncations can be used to define the
functorial action of propositional truncations.

## Definition

```agda
abstract
  unique-map-trunc-Prop :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
    is-contr
      ( Σ ( type-hom-Prop (trunc-Prop A) (trunc-Prop B))
          ( λ h → (h ∘ unit-trunc-Prop) ~ (unit-trunc-Prop ∘ f)))
  unique-map-trunc-Prop {l1} {l2} {A} {B} f =
    universal-property-trunc-Prop A (trunc-Prop B) (unit-trunc-Prop ∘ f)

abstract
  map-trunc-Prop :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} →
    (A → B) → type-hom-Prop (trunc-Prop A) (trunc-Prop B)
  map-trunc-Prop f =
    pr1 (center (unique-map-trunc-Prop f))
```

## Properties

### Propositional truncations of homotopic maps are homotopic

```agda
  htpy-map-trunc-Prop :
    { l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
    ( (map-trunc-Prop f) ∘ unit-trunc-Prop) ~ (unit-trunc-Prop ∘ f)
  htpy-map-trunc-Prop f =
    pr2 (center (unique-map-trunc-Prop f))

  htpy-uniqueness-map-trunc-Prop :
    { l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
    ( h : type-hom-Prop (trunc-Prop A) (trunc-Prop B)) →
    ( ( h ∘ unit-trunc-Prop) ~ (unit-trunc-Prop ∘ f)) →
    (map-trunc-Prop f) ~ h
  htpy-uniqueness-map-trunc-Prop f h H =
    htpy-eq (ap pr1 (contraction (unique-map-trunc-Prop f) (pair h H)))
```

### The propositional truncation of the identity map is the identity map

```agda
abstract
  id-map-trunc-Prop :
    { l1 : Level} {A : UU l1} → map-trunc-Prop (id {A = A}) ~ id
  id-map-trunc-Prop {l1} {A} =
    htpy-uniqueness-map-trunc-Prop id id refl-htpy
```

### The propositional truncation of a composite is the composite of the propositional truncations

```agda
abstract
  preserves-comp-map-trunc-Prop :
    { l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
    ( g : B → C) (f : A → B) →
    ( map-trunc-Prop (g ∘ f)) ~
    ( (map-trunc-Prop g) ∘ (map-trunc-Prop f))
  preserves-comp-map-trunc-Prop g f =
    htpy-uniqueness-map-trunc-Prop
      ( g ∘ f)
      ( (map-trunc-Prop g) ∘ (map-trunc-Prop f))
      ( ( (map-trunc-Prop g) ·l (htpy-map-trunc-Prop f)) ∙h
        ( ( htpy-map-trunc-Prop g) ·r f))
```

### The functorial action of propositional truncations preserves equivalences

```agda
abstract
  map-equiv-trunc-Prop :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} →
    (A ≃ B) → type-trunc-Prop A → type-trunc-Prop B
  map-equiv-trunc-Prop e = map-trunc-Prop (map-equiv e)

abstract
  map-inv-equiv-trunc-Prop :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} →
    (A ≃ B) → type-trunc-Prop B → type-trunc-Prop A
  map-inv-equiv-trunc-Prop e = map-equiv-trunc-Prop (inv-equiv e)

abstract
  equiv-trunc-Prop :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} →
    (A ≃ B) → (type-trunc-Prop A ≃ type-trunc-Prop B)
  pr1 (equiv-trunc-Prop e) = map-equiv-trunc-Prop e
  pr2 (equiv-trunc-Prop e) =
    is-equiv-is-prop
      ( is-prop-type-trunc-Prop)
      ( is-prop-type-trunc-Prop)
      ( map-inv-equiv-trunc-Prop e)
```
