# Decidable equivalence relations on finite types

```agda
module univalent-combinatorics.decidable-equivalence-relations where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.binary-relations
open import foundation.cartesian-product-types
open import foundation.decidable-equality
open import foundation.decidable-equivalence-relations
open import foundation.decidable-relations
open import foundation.decidable-types
open import foundation.equivalence-relations
open import foundation.equivalences
open import foundation.functions
open import foundation.functoriality-cartesian-product-types
open import foundation.functoriality-dependent-pair-types
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.type-arithmetic-cartesian-product-types
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.universe-levels

open import univalent-combinatorics.cartesian-product-types
open import univalent-combinatorics.counting
open import univalent-combinatorics.decidable-propositions
open import univalent-combinatorics.dependent-function-types
open import univalent-combinatorics.dependent-pair-types
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.function-types
open import univalent-combinatorics.standard-finite-types
open import univalent-combinatorics.surjective-maps
```

</details>

## Idea

A decidable equivalence relation on a finite type is an equivalence relation `R`
such that each `R x y` is a decidable proposition.

## Definition

```agda
Decidable-Equivalence-Relation-𝔽 :
  {l1 : Level} (l2 : Level) (X : 𝔽 l1) → UU (l1 ⊔ lsuc l2)
Decidable-Equivalence-Relation-𝔽 l2 X =
  Decidable-Equivalence-Relation l2 (type-𝔽 X)

module _
  {l1 l2 : Level} (X : 𝔽 l1) (R : Decidable-Equivalence-Relation-𝔽 l2 X)
  where

  decidable-relation-Decidable-Equivalence-Relation-𝔽 :
    Decidable-Relation l2 (type-𝔽 X)
  decidable-relation-Decidable-Equivalence-Relation-𝔽 =
    decidable-relation-Decidable-Equivalence-Relation R

  relation-Decidable-Equivalence-Relation-𝔽 :
    type-𝔽 X → type-𝔽 X → Prop l2
  relation-Decidable-Equivalence-Relation-𝔽 =
    relation-Decidable-Equivalence-Relation R

  sim-Decidable-Equivalence-Relation-𝔽 : type-𝔽 X → type-𝔽 X → UU l2
  sim-Decidable-Equivalence-Relation-𝔽 =
    sim-Decidable-Equivalence-Relation R

  is-prop-sim-Decidable-Equivalence-Relation-𝔽 :
    (x y : type-𝔽 X) → is-prop (sim-Decidable-Equivalence-Relation-𝔽 x y)
  is-prop-sim-Decidable-Equivalence-Relation-𝔽 =
    is-prop-sim-Decidable-Equivalence-Relation R

  is-decidable-sim-Decidable-Equivalence-Relation-𝔽 :
    (x y : type-𝔽 X) → is-decidable (sim-Decidable-Equivalence-Relation-𝔽 x y)
  is-decidable-sim-Decidable-Equivalence-Relation-𝔽 =
    is-decidable-sim-Decidable-Equivalence-Relation R

  is-equivalence-relation-Decidable-Equivalence-Relation-𝔽 :
    is-equivalence-relation relation-Decidable-Equivalence-Relation-𝔽
  is-equivalence-relation-Decidable-Equivalence-Relation-𝔽 =
    is-equivalence-relation-Decidable-Equivalence-Relation R

  equivalence-relation-Decidable-Equivalence-Relation-𝔽 :
    Eq-Rel l2 (type-𝔽 X)
  equivalence-relation-Decidable-Equivalence-Relation-𝔽 =
    equivalence-relation-Decidable-Equivalence-Relation R

  refl-Decidable-Equivalence-Relation-𝔽 :
    {x : type-𝔽 X} → sim-Decidable-Equivalence-Relation-𝔽 x x
  refl-Decidable-Equivalence-Relation-𝔽 =
    refl-Decidable-Equivalence-Relation R

  symmetric-Decidable-Equivalence-Relation-𝔽 :
    {x y : type-𝔽 X} → sim-Decidable-Equivalence-Relation-𝔽 x y →
    sim-Decidable-Equivalence-Relation-𝔽 y x
  symmetric-Decidable-Equivalence-Relation-𝔽 =
    symmetric-Decidable-Equivalence-Relation R

  transitive-Decidable-Equivalence-Relation-𝔽 :
    {x y z : type-𝔽 X} → sim-Decidable-Equivalence-Relation-𝔽 x y →
    sim-Decidable-Equivalence-Relation-𝔽 y z →
    sim-Decidable-Equivalence-Relation-𝔽 x z
  transitive-Decidable-Equivalence-Relation-𝔽 =
    transitive-Decidable-Equivalence-Relation R

module _
  {l1 l2 : Level} (A : 𝔽 l1) (R : Decidable-Relation l2 (type-𝔽 A))
  where

  is-finite-relation-Decidable-Relation-𝔽 :
    (x : type-𝔽 A) → (y : type-𝔽 A) → is-finite (type-Decidable-Relation R x y)
  is-finite-relation-Decidable-Relation-𝔽 x y =
     unit-trunc-Prop
       ( count-decidable-Prop
         ( relation-Decidable-Relation R x y )
         ( is-decidable-type-Decidable-Relation R x y))

  is-finite-is-reflexive-Dec-Rel-Prop-𝔽 :
    is-finite (is-reflexive-Rel-Prop (relation-Decidable-Relation R))
  is-finite-is-reflexive-Dec-Rel-Prop-𝔽 =
    is-finite-Π'
      ( is-finite-type-𝔽 A)
      (λ x → is-finite-relation-Decidable-Relation-𝔽 x x )

  is-finite-is-symmetric-Dec-Rel-Prop-𝔽 :
    is-finite (is-symmetric-Rel-Prop (relation-Decidable-Relation R))
  is-finite-is-symmetric-Dec-Rel-Prop-𝔽 =
    is-finite-Π'
      ( is-finite-type-𝔽 A)
      ( λ x →
         is-finite-Π'
           ( is-finite-type-𝔽 A)
           ( λ y →
             is-finite-function-type
               ( is-finite-relation-Decidable-Relation-𝔽 x y)
               ( is-finite-relation-Decidable-Relation-𝔽 y x)))

  is-finite-is-transitive-Dec-Rel-Prop-𝔽 :
    is-finite (is-transitive-Rel-Prop (relation-Decidable-Relation R))
  is-finite-is-transitive-Dec-Rel-Prop-𝔽 =
    is-finite-Π'
      ( is-finite-type-𝔽 A)
      ( λ x →
        is-finite-Π'
          ( is-finite-type-𝔽 A)
          ( λ y →
            is-finite-Π'
              ( is-finite-type-𝔽 A)
              ( λ z →
                is-finite-function-type
                  ( is-finite-relation-Decidable-Relation-𝔽 x y)
                  ( is-finite-function-type
                     ( is-finite-relation-Decidable-Relation-𝔽 y z)
                     ( is-finite-relation-Decidable-Relation-𝔽 x z)) )))

  is-finite-is-equivalence-Dec-Rel-Prop-𝔽 :
    is-finite (is-equivalence-relation (relation-Decidable-Relation R))
  is-finite-is-equivalence-Dec-Rel-Prop-𝔽 =
    is-finite-prod
      ( is-finite-is-reflexive-Dec-Rel-Prop-𝔽)
      ( is-finite-prod
          is-finite-is-symmetric-Dec-Rel-Prop-𝔽
          is-finite-is-transitive-Dec-Rel-Prop-𝔽)
```

## Properties

#### The type of decidable equivalence relations on `A` is equivalent to the type of surjections from `A` into a finite type.

```agda
equiv-Surjection-𝔽-Decidable-Equivalence-Relation-𝔽 :
  {l1 : Level} (A : 𝔽 l1) →
  Decidable-Equivalence-Relation-𝔽 l1 A ≃
  Surjection-𝔽 l1 A
equiv-Surjection-𝔽-Decidable-Equivalence-Relation-𝔽 A =
  ( equiv-Σ-equiv-base
      ( λ X → (type-𝔽 A) ↠ (type-𝔽 X))
      ( equiv-Σ
          ( λ X → is-finite X)
          ( id-equiv)
          ( λ X →
            inv-equiv is-finite-iff-∃-surjection-has-decidable-equality)) ∘e
    ( ( inv-assoc-Σ
          ( UU _)
          ( λ X →
              has-decidable-equality X ×
              type-trunc-Prop (Σ ℕ (λ n → Fin n ↠  X)))
          ( λ X → type-𝔽 A ↠ pr1 X)  ) ∘e
      ( ( equiv-Σ
            (λ X →
                Σ ( has-decidable-equality X ×
                    type-trunc-Prop (Σ ℕ (λ n → Fin n ↠ X)))
                  ( λ _ → pr1 A ↠ X))
            ( id-equiv)
            ( λ X →
              ( ( inv-equiv
                  ( assoc-prod
                    ( has-decidable-equality X)
                    ( type-trunc-Prop (Σ ℕ (λ n → Fin n ↠ X)))
                    ( type-𝔽 A ↠ X))) ∘e
                ( ( equiv-prod id-equiv commutative-prod) ∘e
                  ( ( assoc-prod
                      ( has-decidable-equality (map-equiv id-equiv X))
                      ( type-𝔽 A ↠ X)
                      ( type-trunc-Prop (Σ ℕ (λ n → Fin n ↠ X)))) ∘e
                  ( ( equiv-prod commutative-prod id-equiv)  ∘e
                    ( ( equiv-add-redundant-prop
                        ( is-prop-type-trunc-Prop)
                        ( λ x →
                           apply-universal-property-trunc-Prop
                             ( is-finite-type-𝔽 A)
                             ( trunc-Prop ( Σ ℕ (λ n → Fin n ↠ X)))
                             ( λ count-A →
                               unit-trunc-Prop
                                 ( number-of-elements-count count-A ,
                                   ( ( map-surjection (pr1 x) ∘
                                       map-equiv-count count-A) ,
                                     is-surjective-precomp-equiv
                                       ( is-surjective-map-surjection (pr1 x))
                                       ( equiv-count count-A)))))))))))) ∘e
        ( equiv-Surjection-Into-Set-Decidable-Equivalence-Relation
          ( type-𝔽 A))))))
```

### The type of decidable equivalence relations on a finite type is finite

```agda
is-finite-Decidable-Relation-𝔽 :
  {l1 : Level} (A : 𝔽 l1) →
  is-finite (Decidable-Relation l1 (type-𝔽 A))
is-finite-Decidable-Relation-𝔽 A =
  is-finite-Π
    ( is-finite-type-𝔽 A)
    ( λ a →
      is-finite-Π
        ( is-finite-type-𝔽 A)
        ( λ b → is-finite-decidable-Prop))

is-finite-Decidable-Equivalence-Relation-𝔽 :
  {l1 : Level} (A : 𝔽 l1) →
  is-finite (Decidable-Equivalence-Relation-𝔽 l1 A)
is-finite-Decidable-Equivalence-Relation-𝔽 A =
  is-finite-Σ
    ( is-finite-Decidable-Relation-𝔽 A)
    ( λ R → is-finite-is-equivalence-Dec-Rel-Prop-𝔽 A R)
```

-- ### The number of decidable equivalence relations on a finite type is a
Stirling number of the second kind
