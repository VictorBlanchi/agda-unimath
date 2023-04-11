# Coproducts of species of types of subuniverse

```agda
module species.coproducts-species-of-types-in-subuniverse where
```

<details><summary>Imports</summary>

```agda
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.functions
open import foundation.homotopies
open import foundation.identity-types
open import foundation.subuniverses
open import foundation.universe-levels

open import species.coproducts-species-of-types
open import species.species-of-types-in-subuniverse
```

</details>

## Idea

The coproduct of two species of types of subuniverse `F` and `G` is the
pointwise coproduct provided that the domain subuniverse of `F` and `G` is
stable by coproduct.

## Definition

```agda
module _
  {l1 l2 l3 : Level} (P : subuniverse l1 l1) (Q : global-subuniverse id )
  where

  coproduct-species-subuniverse' :
    (S : species-subuniverse P (subuniverse-global-subuniverse Q l2))
    (T : species-subuniverse P (subuniverse-global-subuniverse Q l3))
    (X : type-subuniverse P) → UU (l2 ⊔ l3)
  coproduct-species-subuniverse' S T X =
    inclusion-subuniverse
      ( subuniverse-global-subuniverse Q l2)
      ( S X) +
    inclusion-subuniverse
      ( subuniverse-global-subuniverse Q l3)
      ( T X)

module _
  {l1 l2 l3 : Level} (P : subuniverse l1 l1) (Q : global-subuniverse id )
  ( C1 :
    ( (l4 l5 : Level)
    (S : species-subuniverse P (subuniverse-global-subuniverse Q l4))
    (T : species-subuniverse P (subuniverse-global-subuniverse Q l5))
    (X : type-subuniverse P) →
      is-in-subuniverse
        ( subuniverse-global-subuniverse Q (l4 ⊔ l5))
        ( coproduct-species-subuniverse' P Q S T X)))
  where

  coproduct-species-subuniverse :
    species-subuniverse P (subuniverse-global-subuniverse Q l2) →
    species-subuniverse P (subuniverse-global-subuniverse Q l3) →
    species-subuniverse P (subuniverse-global-subuniverse Q (l2 ⊔ l3))
  pr1 (coproduct-species-subuniverse S T X) =
    coproduct-species-subuniverse' P Q S T X
  pr2 (coproduct-species-subuniverse S T X) = C1 l2 l3 S T X
```

## Properties

### Equivalent form with species of types

```agda
module _
  {l1 l2 l3 : Level} (P : subuniverse l1 l1) (Q : global-subuniverse id )
  ( C1 :
    ( (l4 l5 : Level)
    (S : species-subuniverse P (subuniverse-global-subuniverse Q l4))
    (T : species-subuniverse P (subuniverse-global-subuniverse Q l5))
    (X : type-subuniverse P) →
      is-in-subuniverse
        ( subuniverse-global-subuniverse Q (l4 ⊔ l5))
        ( coproduct-species-subuniverse' P Q S T X)))
  ( S : species-subuniverse P (subuniverse-global-subuniverse Q l2))
  ( T : species-subuniverse P (subuniverse-global-subuniverse Q l3))
  ( X : UU l1)
  where

  map-coproduct-Σ-extension-species-subuniverse :
    Σ-extension-species-subuniverse
      ( P)
      ( subuniverse-global-subuniverse Q (l2 ⊔ l3))
      ( coproduct-species-subuniverse P Q C1 S T)
      ( X) →
    coproduct-species-types
      ( Σ-extension-species-subuniverse
          ( P)
          ( subuniverse-global-subuniverse Q l2)
          ( S))
      ( Σ-extension-species-subuniverse
          ( P)
          ( subuniverse-global-subuniverse Q l3)
          ( T))
      ( X)
  map-coproduct-Σ-extension-species-subuniverse (p , inl x) = inl ( p , x)
  map-coproduct-Σ-extension-species-subuniverse (p , inr x) = inr ( p , x)

  map-inv-coproduct-Σ-extension-species-subuniverse :
    coproduct-species-types
      ( Σ-extension-species-subuniverse
          ( P)
          ( subuniverse-global-subuniverse Q l2)
          ( S))
      ( Σ-extension-species-subuniverse
          ( P)
          ( subuniverse-global-subuniverse Q l3)
          ( T))
      ( X) →
    Σ-extension-species-subuniverse
      ( P)
      ( subuniverse-global-subuniverse Q (l2 ⊔ l3))
      ( coproduct-species-subuniverse P Q C1 S T)
      ( X)
  map-inv-coproduct-Σ-extension-species-subuniverse (inl x) = pr1 x , inl (pr2 x)
  map-inv-coproduct-Σ-extension-species-subuniverse (inr x) = pr1 x , inr (pr2 x)

  issec-map-inv-coproduct-Σ-extension-species-subuniverse :
    ( map-coproduct-Σ-extension-species-subuniverse ∘
      map-inv-coproduct-Σ-extension-species-subuniverse) ~
    id
  issec-map-inv-coproduct-Σ-extension-species-subuniverse (inl (p , x)) =
    refl
  issec-map-inv-coproduct-Σ-extension-species-subuniverse (inr (p , x)) =
    refl

  isretr-map-inv-coproduct-Σ-extension-species-subuniverse :
    ( map-inv-coproduct-Σ-extension-species-subuniverse ∘
      map-coproduct-Σ-extension-species-subuniverse) ~
    id
  isretr-map-inv-coproduct-Σ-extension-species-subuniverse (p , inl x) =
    refl
  isretr-map-inv-coproduct-Σ-extension-species-subuniverse (p , inr x) =
    refl

  equiv-coproduct-Σ-extension-species-subuniverse :
    Σ-extension-species-subuniverse
      ( P)
      ( subuniverse-global-subuniverse Q (l2 ⊔ l3))
      ( coproduct-species-subuniverse P Q C1 S T)
      ( X) ≃
    coproduct-species-types
      ( Σ-extension-species-subuniverse
          ( P)
          ( subuniverse-global-subuniverse Q l2)
          ( S))
      ( Σ-extension-species-subuniverse
          ( P)
          ( subuniverse-global-subuniverse Q l3)
          ( T))
      ( X)
  pr1 equiv-coproduct-Σ-extension-species-subuniverse =
    map-coproduct-Σ-extension-species-subuniverse
  pr2 equiv-coproduct-Σ-extension-species-subuniverse =
    is-equiv-has-inverse
      map-inv-coproduct-Σ-extension-species-subuniverse
      issec-map-inv-coproduct-Σ-extension-species-subuniverse
      isretr-map-inv-coproduct-Σ-extension-species-subuniverse
```
