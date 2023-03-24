# Dirichlet series of species of finite inhabited types

```agda
module species.dirichlet-series-of-species-of-inhabited-finite-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import species.species-of-finite-inhabited-types

open import elementary-number-theory.natural-numbers

open import univalent-combinatorics.cyclic-types
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.inhabited-finite-types
```

</details>

## Idea

## Definition

```agda
dirichlet-serie-species-inhabited-𝔽 :
  {l1 l2 : Level} (l3 : Level) →
  (F : species-Inhabited-Type-𝔽 l1 l2) →
  (S : UU l3) →
  UU (lsuc l1 ⊔ l2 ⊔ lsuc l3)
dirichlet-serie-species-inhabited-𝔽 {l1} l3 F S =
  Σ ℕ
    ( λ n →
      ( Σ ( UU-Fin l1 (succ-ℕ n))
          ( λ X → type-𝔽
            ( F
              ( type-UU-Fin (succ-ℕ n) X ,
                is-finite-and-inhabited-UU-Fin n X)))) ×
      ( S → Cyclic-Type l3 n))
```
