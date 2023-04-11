# Inhabited finite types

```agda
module univalent-combinatorics.inhabited-finite-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.equivalences
open import foundation.functions
open import foundation.functoriality-dependent-function-types
open import foundation.identity-types
open import foundation.inhabited-types
open import foundation.propositions
open import foundation.subtypes
open import foundation.subuniverses
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.type-theoretic-principle-of-choice
open import foundation.universe-levels

open import univalent-combinatorics.dependent-pair-types
open import univalent-combinatorics.finite-types
```

</details>

## Idea

## Definitions

### Inhabited finite types

```agda
Inhabited-Type-𝔽 : (l : Level) → UU (lsuc l)
Inhabited-Type-𝔽 l = Σ ( 𝔽 l) ( λ X → is-inhabited (type-𝔽 X))

module _
  {l : Level} (X : Inhabited-Type-𝔽 l)
  where

  finite-type-Inhabited-Type-𝔽 : 𝔽 l
  finite-type-Inhabited-Type-𝔽 = pr1 X

  type-Inhabited-Type-𝔽 : UU l
  type-Inhabited-Type-𝔽 = type-𝔽 finite-type-Inhabited-Type-𝔽

  is-finite-Inhabited-Type-𝔽 : is-finite type-Inhabited-Type-𝔽
  is-finite-Inhabited-Type-𝔽 = is-finite-type-𝔽 finite-type-Inhabited-Type-𝔽

  is-inhabited-type-Inhabited-Type-𝔽 : is-inhabited type-Inhabited-Type-𝔽
  is-inhabited-type-Inhabited-Type-𝔽 = pr2 X

  inhabited-type-Inhabited-Type-𝔽 : Inhabited-Type l
  pr1 inhabited-type-Inhabited-Type-𝔽 = type-Inhabited-Type-𝔽
  pr2 inhabited-type-Inhabited-Type-𝔽 = is-inhabited-type-Inhabited-Type-𝔽

compute-Inhabited-Type-𝔽 :
  {l : Level} →
  Inhabited-Type-𝔽 l ≃
    Σ (Inhabited-Type l ) (λ X → is-finite (type-Inhabited-Type X))
compute-Inhabited-Type-𝔽 = equiv-right-swap-Σ

is-finite-and-inhabited-Prop : {l : Level} → UU l → Prop l
is-finite-and-inhabited-Prop X =
  prod-Prop (is-finite-Prop X) (is-inhabited-Prop X)

is-finite-and-inhabited : {l : Level} → UU l → UU l
is-finite-and-inhabited X =
  type-Prop (is-finite-and-inhabited-Prop X)

compute-Inhabited-Type-𝔽' :
  {l : Level} →
  Inhabited-Type-𝔽 l ≃ type-subuniverse is-finite-and-inhabited-Prop
compute-Inhabited-Type-𝔽' = assoc-Σ _ _ _

map-compute-Inhabited-Type-𝔽' :
  {l : Level} →
  Inhabited-Type-𝔽 l → type-subuniverse is-finite-and-inhabited-Prop
map-compute-Inhabited-Type-𝔽' = map-assoc-Σ _ _ _

map-inv-compute-Inhabited-Type-𝔽' :
  {l : Level} →
  type-subuniverse is-finite-and-inhabited-Prop → Inhabited-Type-𝔽 l
map-inv-compute-Inhabited-Type-𝔽' = map-inv-assoc-Σ _ _ _
```

### Families of inhabited types

```agda
Fam-Inhabited-Types-𝔽 :
  {l1 : Level} → (l2 : Level) → (X : 𝔽 l1) → UU (l1 ⊔ lsuc l2)
Fam-Inhabited-Types-𝔽 l2 X = type-𝔽 X → Inhabited-Type-𝔽 l2

module _
  {l1 l2 : Level} (X : 𝔽 l1) (Y : Fam-Inhabited-Types-𝔽 l2 X)
    where

  type-Fam-Inhabited-Types-𝔽 : type-𝔽 X → UU l2
  type-Fam-Inhabited-Types-𝔽 x = type-Inhabited-Type-𝔽 (Y x)

  finite-type-Fam-Inhabited-Types-𝔽 : type-𝔽 X → 𝔽 l2
  pr1 (finite-type-Fam-Inhabited-Types-𝔽 x) = type-Fam-Inhabited-Types-𝔽 x
  pr2 (finite-type-Fam-Inhabited-Types-𝔽 x) = is-finite-Inhabited-Type-𝔽 (Y x)

  is-inhabited-type-Fam-Inhabited-Types-𝔽 :
    (x : type-𝔽 X) → is-inhabited (type-Fam-Inhabited-Types-𝔽 x)
  is-inhabited-type-Fam-Inhabited-Types-𝔽 x =
    is-inhabited-type-Inhabited-Type-𝔽 (Y x)

  total-Fam-Inhabited-Types-𝔽 : 𝔽 (l1 ⊔ l2)
  total-Fam-Inhabited-Types-𝔽 = Σ-𝔽 X finite-type-Fam-Inhabited-Types-𝔽

compute-Fam-Inhabited-Type-𝔽 :
  {l1 l2 : Level} → (X : 𝔽 l1) →
  Fam-Inhabited-Types-𝔽 l2 X ≃
    Σ ( Fam-Inhabited-Types l2 (type-𝔽 X))
      ( λ Y → ((x : (type-𝔽 X)) → is-finite (type-Inhabited-Type (Y x))))
compute-Fam-Inhabited-Type-𝔽 X =
   ( distributive-Π-Σ ∘e
    ( equiv-Π
      ( λ _ → Σ (Inhabited-Type _) ( is-finite ∘ type-Inhabited-Type))
      ( id-equiv)
      ( λ _ → compute-Inhabited-Type-𝔽)))
```

## Proposition

### Equality in inhabited finite types

```agda
eq-equiv-Inhabited-Type-𝔽 :
  {l : Level} → (X Y : Inhabited-Type-𝔽 l) →
  type-Inhabited-Type-𝔽 X ≃ type-Inhabited-Type-𝔽 Y → X ＝ Y
eq-equiv-Inhabited-Type-𝔽 X Y e =
  eq-type-subtype
    ( λ X  → is-inhabited-Prop (type-𝔽 X))
    ( eq-equiv-𝔽
      ( finite-type-Inhabited-Type-𝔽 X)
      ( finite-type-Inhabited-Type-𝔽 Y)
      ( e))
```
