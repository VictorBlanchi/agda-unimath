# Small types

```agda
module foundation.small-types where
```

<details><summary>Imports</summary>

```agda
open import foundation-core.small-types public

open import foundation.images
open import foundation.locally-small-types
open import foundation.replacement
open import foundation.surjective-maps
open import foundation.uniqueness-image
open import foundation.universal-property-image

open import foundation-core.dependent-pair-types
open import foundation-core.embeddings
open import foundation-core.homotopies
open import foundation-core.universe-levels
```

</details>

## Properties

### If `f` is a surjective map from a small type into a locally small type, then `Replacement` implies that the codomain is small

```agda
is-small-is-surjective :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {f : A → B} →
  is-surjective f → is-small l3 A → is-locally-small l3 B →
  is-small l3 B
is-small-is-surjective {f = f} H K L =
  is-small-equiv'
    ( im f)
    ( equiv-equiv-slice-uniqueness-im f id-emb
      ( pair f refl-htpy)
      ( is-image-is-surjective f id-emb (pair f refl-htpy) H))
    ( replacement f K L)
```
