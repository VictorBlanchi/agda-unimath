# Quotient algebras

```agda
module universal-algebra.quotient-algebras where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.equivalence-classes
open import foundation.equivalence-relations
open import foundation.equivalences
open import foundation.functoriality-propositional-truncation
open import foundation.multivariable-functoriality-set-quotients
open import foundation.multivariable-operations
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.set-quotients
open import foundation.sets
open import foundation.unit-type
open import foundation.universe-levels
open import foundation.vectors-set-quotients

open import linear-algebra.vectors

open import universal-algebra.algebraic-theories
open import universal-algebra.algebras-of-theories
open import universal-algebra.congruences
open import universal-algebra.models-of-signatures
open import universal-algebra.signatures
```

</details>

## Idea

The quotient of an algebra by a congruence is the set quotient by that
congruence. This quotient again has the structure of an algebra inherited by the
original one.

## Definitions

```agda
module _
  { l1 : Level} ( Sg : signature l1)
  { l2 : Level} ( Th : Theory Sg l2)
  { l3 : Level} ( Alg : Algebra Sg Th l3)
  { l4 : Level} ( R : congruence-Algebra Sg Th Alg l4)
  where

  set-quotient-Algebra : Set (l3 ⊔ l4)
  set-quotient-Algebra =
    quotient-Set ( eq-rel-congruence-Algebra Sg Th Alg R)

  type-quotient-Algebra : UU (l3 ⊔ l4)
  type-quotient-Algebra = pr1 set-quotient-Algebra

  is-set-set-quotient-Algebra : is-set type-quotient-Algebra
  is-set-set-quotient-Algebra = pr2 set-quotient-Algebra

  compute-quotient-Algebra :
    equivalence-class
      ( eq-rel-congruence-Algebra Sg Th Alg R) ≃
      ( type-quotient-Algebra)
  compute-quotient-Algebra =
    compute-set-quotient
      ( eq-rel-congruence-Algebra Sg Th Alg R)

  set-quotient-equivalence-class-Algebra :
    equivalence-class
      ( eq-rel-congruence-Algebra Sg Th Alg R) →
    type-quotient-Algebra
  set-quotient-equivalence-class-Algebra =
    map-equiv compute-quotient-Algebra

  equivalence-class-set-quotient-Algebra :
    type-quotient-Algebra →
    equivalence-class
      ( eq-rel-congruence-Algebra Sg Th Alg R)
  equivalence-class-set-quotient-Algebra =
    map-inv-equiv compute-quotient-Algebra

  vec-type-quotient-vec-type-Algebra :
    { n : ℕ} →
    vec type-quotient-Algebra n →
    type-trunc-Prop (vec (type-Algebra Sg Th Alg) n)
  vec-type-quotient-vec-type-Algebra empty-vec = unit-trunc-Prop empty-vec
  vec-type-quotient-vec-type-Algebra (x ∷ v) =
    map-universal-property-trunc-Prop
      ( trunc-Prop _)
      ( λ (z , p) →
        map-trunc-Prop
          (λ v' → z ∷ v')
          ( vec-type-quotient-vec-type-Algebra v))
      ( pr2 (equivalence-class-set-quotient-Algebra x))

  relation-holds-all-vec-all-sim-Eq-Rel :
    { n : ℕ}
    ( v v' : multivariable-input n ( λ _ → type-Algebra Sg Th Alg)) →
    ( type-Prop
      ( prop-Eq-Rel
        ( all-sim-Eq-Rel n
          ( λ _ → type-Algebra Sg Th Alg)
          ( λ _ → eq-rel-congruence-Algebra Sg Th Alg R)) v v')) →
    relation-holds-all-vec Sg Th Alg
      ( eq-rel-congruence-Algebra Sg Th Alg R)
      ( vector-multivariable-input n (type-Algebra Sg Th Alg) v)
      ( vector-multivariable-input n (type-Algebra Sg Th Alg) v')
  relation-holds-all-vec-all-sim-Eq-Rel {zero-ℕ} v v' p = raise-star
  relation-holds-all-vec-all-sim-Eq-Rel {succ-ℕ n} (x , v) (x' , v') (p , p') =
    pair p (relation-holds-all-vec-all-sim-Eq-Rel v v' p')

  is-model-set-quotient-Algebra :
    is-model-signature Sg set-quotient-Algebra
  is-model-set-quotient-Algebra op v =
    multivariable-map-set-quotient
      ( arity-operation-signature Sg op)
      ( λ _ → type-Algebra Sg Th Alg)
      ( λ _ → eq-rel-congruence-Algebra Sg Th Alg R)
      ( eq-rel-congruence-Algebra Sg Th Alg R)
      ( pair
        ( λ v →
          is-model-set-Algebra Sg Th Alg op
            ( vector-multivariable-input
              ( arity-operation-signature Sg op)
              ( type-Algebra Sg Th Alg)
              ( v)))
        ( λ {v} {v'} p →
          preserves-operations-congruence-Algebra Sg Th Alg R op
            ( vector-multivariable-input
              ( arity-operation-signature Sg op)
              ( type-Algebra Sg Th Alg)
              ( v))
            ( vector-multivariable-input
              ( arity-operation-signature Sg op)
              ( type-Algebra Sg Th Alg)
              ( v'))
            (relation-holds-all-vec-all-sim-Eq-Rel v v' p)))
      ( multivariable-input-vector
        ( arity-operation-signature Sg op)
        ( type-quotient-Algebra)
        ( v))
```
