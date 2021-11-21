{-# OPTIONS --without-K --exact-split #-}

module foundations.pointed-maps where

open import foundations.24-pushouts public

-- The universe of pointed types

Pointed-Type : (l : Level) → UU (lsuc l)
Pointed-Type l = Σ (UU l) (λ X → X)

module _
  {l : Level} (A : Pointed-Type l)
  where
  
  type-Pointed-Type : UU l
  type-Pointed-Type = pr1 A
  
  pt-Pointed-Type : type-Pointed-Type
  pt-Pointed-Type = pr2 A

-- Pointed families

Pointed-Fam :
  {l1 : Level} (l : Level) (A : Pointed-Type l1) → UU (lsuc l ⊔ l1)
Pointed-Fam l A = Σ (type-Pointed-Type A → UU l) (λ P → P (pt-Pointed-Type A))

module _
  {l1 l2 : Level} (A : Pointed-Type l1) (B : Pointed-Fam l2 A)
  where
  
  fam-Pointed-Fam : type-Pointed-Type A → UU l2
  fam-Pointed-Fam = pr1 B

  pt-Pointed-Fam : fam-Pointed-Fam (pt-Pointed-Type A)
  pt-Pointed-Fam = pr2 B

  -- Pointed Π-types

  pointed-Π : UU (l1 ⊔ l2)
  pointed-Π =
    Σ ( (x : type-Pointed-Type A) → fam-Pointed-Fam x)
      ( λ f → Id (f (pt-Pointed-Type A)) pt-Pointed-Fam)

  function-pointed-Π : pointed-Π → (x : type-Pointed-Type A) → fam-Pointed-Fam x
  function-pointed-Π f = pr1 f

  preserves-point-function-pointed-Π :
    (f : pointed-Π) →
    Id (function-pointed-Π f (pt-Pointed-Type A)) pt-Pointed-Fam
  preserves-point-function-pointed-Π f = pr2 f

module _
  {l1 l2 : Level} (A : Pointed-Type l1) (B : Pointed-Fam l2 A)
  (f : pointed-Π A B)
  where

  -- Pointed homotopies

  htpy-pointed-Π : (g : pointed-Π A B) → UU (l1 ⊔ l2)
  htpy-pointed-Π g =
    pointed-Π A
      ( pair
        ( λ x →
          Id ( function-pointed-Π A B f x)
             ( function-pointed-Π A B g x))
        ( ( preserves-point-function-pointed-Π A B f) ∙
          ( inv (preserves-point-function-pointed-Π A B g))))

  refl-htpy-pointed-Π : htpy-pointed-Π f
  refl-htpy-pointed-Π =
    pair refl-htpy (inv (right-inv (preserves-point-function-pointed-Π A B f)))

  htpy-eq-pointed-Π :
    (g : pointed-Π A B) → Id f g → htpy-pointed-Π g
  htpy-eq-pointed-Π .f refl = refl-htpy-pointed-Π

  is-contr-total-htpy-pointed-Π : is-contr (Σ (pointed-Π A B) htpy-pointed-Π)
  is-contr-total-htpy-pointed-Π =
    is-contr-total-Eq-structure
      ( λ g β (H : function-pointed-Π A B f ~ g) →
          Id ( H (pt-Pointed-Type A))
             ( (preserves-point-function-pointed-Π A B f) ∙ (inv β)))
      ( is-contr-total-htpy (function-pointed-Π A B f))
      ( pair (function-pointed-Π A B f) refl-htpy)
      ( is-contr-equiv'
        ( Σ ( Id ( function-pointed-Π A B f (pt-Pointed-Type A))
                 ( pt-Pointed-Fam A B))
            ( λ β → Id β (preserves-point-function-pointed-Π A B f)))
        ( equiv-tot
          ( λ β →
            equiv-con-inv refl β (preserves-point-function-pointed-Π A B f)))
        ( is-contr-total-path' (preserves-point-function-pointed-Π A B f)))

  is-equiv-htpy-eq-pointed-Π :
    (g : pointed-Π A B) → is-equiv (htpy-eq-pointed-Π g)
  is-equiv-htpy-eq-pointed-Π =
    fundamental-theorem-id f
      ( refl-htpy-pointed-Π)
      ( is-contr-total-htpy-pointed-Π)
      ( htpy-eq-pointed-Π)

  eq-htpy-pointed-Π :
    (g : pointed-Π A B) → (htpy-pointed-Π g) → Id f g
  eq-htpy-pointed-Π g = map-inv-is-equiv (is-equiv-htpy-eq-pointed-Π g)

-- Pointed maps

module _
  {l1 l2 : Level}
  where

  constant-Pointed-Fam :
    (A : Pointed-Type l1) → Pointed-Type l2 → Pointed-Fam l2 A
  constant-Pointed-Fam A B =
    pair (λ x → type-Pointed-Type B) (pt-Pointed-Type B)
  
  _→*_ : Pointed-Type l1 → Pointed-Type l2 → UU (l1 ⊔ l2)
  A →* B = pointed-Π A (constant-Pointed-Fam A B)

  [_→*_] : Pointed-Type l1 → Pointed-Type l2 → Pointed-Type (l1 ⊔ l2)
  [ A →* B ] =
    pair
      ( A →* B)
      ( pair
        ( const (type-Pointed-Type A) (type-Pointed-Type B) (pt-Pointed-Type B))
        ( refl))

module _
  {l1 l2 : Level} (A : Pointed-Type l1) (B : Pointed-Type l2)
  where
  
  map-pointed-map : A →* B → type-Pointed-Type A → type-Pointed-Type B
  map-pointed-map f = pr1 f

  preserves-point-map-pointed-map :
    (f : A →* B) →
    Id (map-pointed-map f (pt-Pointed-Type A)) (pt-Pointed-Type B)
  preserves-point-map-pointed-map f = pr2 f

module _
  {l1 l2 l3 : Level} (A : Pointed-Type l1) (B : Pointed-Type l2)
  (C : Pointed-Fam l3 B) (f : A →* B)
  where

  precomp-Pointed-Fam : Pointed-Fam l3 A
  precomp-Pointed-Fam =
    pair
      ( fam-Pointed-Fam B C ∘ map-pointed-map A B f)
      ( tr
        ( fam-Pointed-Fam B C)
        ( inv (preserves-point-map-pointed-map A B f))
        ( pt-Pointed-Fam B C))

  precomp-pointed-Π : pointed-Π B C → pointed-Π A precomp-Pointed-Fam
  precomp-pointed-Π g =
    pair
      ( λ x → function-pointed-Π B C g (map-pointed-map A B f x))
      ( ( inv
          ( apd
            ( function-pointed-Π B C g)
            ( inv (preserves-point-map-pointed-map A B f)))) ∙
        ( ap
          ( tr
            ( fam-Pointed-Fam B C)
            ( inv (preserves-point-map-pointed-map A B f)))
          ( preserves-point-function-pointed-Π B C g)))

module _
  {l1 l2 l3 : Level} (A : Pointed-Type l1) (B : Pointed-Type l2)
  (C : Pointed-Type l3)
  where

  precomp-pointed-map : A →* B → B →* C → A →* C
  precomp-pointed-map f g =
    pair
      ( map-pointed-map B C g ∘ map-pointed-map A B f)
      ( ( ap (map-pointed-map B C g) (preserves-point-map-pointed-map A B f)) ∙
        ( preserves-point-map-pointed-map B C g))

  comp-pointed-map : B →* C → A →* B → A →* C
  comp-pointed-map g f = precomp-pointed-map f g

module _
  {l1 : Level} (A : Pointed-Type l1)
  where

  id-pointed-map : A →* A
  id-pointed-map = pair id refl

module _
  {l1 l2 : Level} (A : Pointed-Type l1) (B : Pointed-Type l2) (f : A →* B)
  where

  -- Pointed homotopies of pointed maps

  htpy-pointed-map : (g : A →* B) → UU (l1 ⊔ l2)
  htpy-pointed-map = htpy-pointed-Π A (constant-Pointed-Fam A B) f

  refl-htpy-pointed-map : htpy-pointed-map f
  refl-htpy-pointed-map = refl-htpy-pointed-Π A (constant-Pointed-Fam A B) f

  htpy-eq-pointed-map :
    (g : A →* B) → Id f g → htpy-pointed-map g
  htpy-eq-pointed-map = htpy-eq-pointed-Π A (constant-Pointed-Fam A B) f

  is-contr-total-htpy-pointed-map : is-contr (Σ (A →* B) htpy-pointed-map)
  is-contr-total-htpy-pointed-map =
    is-contr-total-htpy-pointed-Π A (constant-Pointed-Fam A B) f

  is-equiv-htpy-eq-pointed-map :
    (g : A →* B) → is-equiv (htpy-eq-pointed-map g)
  is-equiv-htpy-eq-pointed-map =
    is-equiv-htpy-eq-pointed-Π A (constant-Pointed-Fam A B) f

  eq-htpy-pointed-map :
    (g : A →* B) → (htpy-pointed-map g) → Id f g
  eq-htpy-pointed-map = eq-htpy-pointed-Π A (constant-Pointed-Fam A B) f

-- Pointed equivalences

module _
  {l1 l2 : Level} (A : Pointed-Type l1) (B : Pointed-Type l2) (f : A →* B)
  where

  sec-pointed-map : UU (l1 ⊔ l2)
  sec-pointed-map =
    Σ ( B →* A)
      ( λ g →
        htpy-pointed-map B B
          ( comp-pointed-map B A B f g)
          ( id-pointed-map B))

  retr-pointed-map : UU (l1 ⊔ l2)
  retr-pointed-map =
    Σ ( B →* A)
      ( λ g →
        htpy-pointed-map A A
          ( comp-pointed-map A B A g f)
          ( id-pointed-map A))

  is-iso-pointed-map : UU (l1 ⊔ l2)
  is-iso-pointed-map = sec-pointed-map × retr-pointed-map

  is-equiv-pointed-map : UU (l1 ⊔ l2)
  is-equiv-pointed-map = is-equiv (map-pointed-map A B f)

  is-contr-sec-is-equiv-pointed-map :
    is-equiv-pointed-map → is-contr sec-pointed-map
  is-contr-sec-is-equiv-pointed-map H =
    is-contr-total-Eq-structure
      ( λ g p (G : (map-pointed-map A B f ∘ g) ~ id) →
          Id { A = Id { A = type-Pointed-Type B}
                      ( map-pointed-map A B f (g (pt-Pointed-Type B)))
                      ( pt-Pointed-Type B)}
             ( G (pt-Pointed-Type B))
             ( ( ( ap (map-pointed-map A B f) p) ∙
                 ( preserves-point-map-pointed-map A B f)) ∙
               ( refl)))
      ( is-contr-sec-is-equiv H)
      ( pair (map-inv-is-equiv H) (issec-map-inv-is-equiv H))
      ( is-contr-equiv
        ( fib
          ( ap (map-pointed-map A B f))
          ( ( issec-map-inv-is-equiv H (pt-Pointed-Type B)) ∙
            ( inv (preserves-point-map-pointed-map A B f))))
        ( equiv-tot
          ( λ p →
            ( ( equiv-con-inv
                ( ap (map-pointed-map A B f) p)
                ( preserves-point-map-pointed-map A B f)
                ( issec-map-inv-is-equiv H (pt-Pointed-Type B))) ∘e
              ( equiv-inv
                ( issec-map-inv-is-equiv H (pt-Pointed-Type B))
                ( ( ap (map-pointed-map A B f) p) ∙
                  ( preserves-point-map-pointed-map A B f)))) ∘e
            ( equiv-concat'
              ( issec-map-inv-is-equiv H (pt-Pointed-Type B))
              ( right-unit))))
        ( is-contr-map-is-equiv
          ( is-emb-is-equiv H
            ( map-inv-is-equiv H (pt-Pointed-Type B))
            ( pt-Pointed-Type A))
          ( ( issec-map-inv-is-equiv H (pt-Pointed-Type B)) ∙
            ( inv (preserves-point-map-pointed-map A B f)))))

  is-contr-retr-is-equiv-pointed-map :
    is-equiv-pointed-map → is-contr retr-pointed-map
  is-contr-retr-is-equiv-pointed-map H =
    is-contr-total-Eq-structure
      ( λ g p (G : (g ∘ map-pointed-map A B f) ~ id) →
        Id {A = Id { A = type-Pointed-Type A}
                   ( g (map-pointed-map A B f (pt-Pointed-Type A)))
                   ( pt-Pointed-Type A)}
           ( G (pt-Pointed-Type A))
           ( ( ( ap g (preserves-point-map-pointed-map A B f)) ∙
               ( p)) ∙
             ( refl)))
      ( is-contr-retr-is-equiv H)
      ( pair (map-inv-is-equiv H) (isretr-map-inv-is-equiv H))
      ( is-contr-equiv
        ( fib
          ( λ p →
            ( ( ap
                ( map-inv-is-equiv H)
                ( preserves-point-map-pointed-map A B f)) ∙
              ( p)) ∙
            ( refl))
          ( isretr-map-inv-is-equiv H (pt-Pointed-Type A)))
        ( equiv-tot (λ p → equiv-inv _ _))
        ( is-contr-map-is-equiv
          ( is-equiv-comp'
            ( λ q → q ∙ refl)
            ( λ p →
              ( ap
                ( map-inv-is-equiv H)
                ( preserves-point-map-pointed-map A B f)) ∙
              ( p))
            ( is-equiv-concat
              ( ap
                ( map-inv-is-equiv H)
                ( preserves-point-map-pointed-map A B f))
              ( pt-Pointed-Type A))
            ( is-equiv-concat'
              ( map-inv-is-equiv H (map-pointed-map A B f (pt-Pointed-Type A)))
              ( refl)))
          ( isretr-map-inv-is-equiv H (pt-Pointed-Type A))))

  is-contr-is-iso-is-equiv-pointed-map :
    is-equiv-pointed-map → is-contr is-iso-pointed-map
  is-contr-is-iso-is-equiv-pointed-map H =
    is-contr-prod
      ( is-contr-sec-is-equiv-pointed-map H)
      ( is-contr-retr-is-equiv-pointed-map H)

  is-iso-is-equiv-pointed-map :
    is-equiv-pointed-map → is-iso-pointed-map
  is-iso-is-equiv-pointed-map H =
    center (is-contr-is-iso-is-equiv-pointed-map H)

  is-equiv-is-iso-pointed-map :
    is-iso-pointed-map → is-equiv-pointed-map
  is-equiv-is-iso-pointed-map H =
    pair
      ( pair
        ( pr1 (pr1 (pr1 H)))
        ( pr1 (pr2 (pr1 H))))
      ( pair
        ( pr1 (pr1 (pr2 H)))
        ( pr1 (pr2 (pr2 H))))

  is-prop-is-iso-pointed-map : is-prop is-iso-pointed-map
  is-prop-is-iso-pointed-map =
    is-prop-is-proof-irrelevant
      ( λ H →
        is-contr-is-iso-is-equiv-pointed-map (is-equiv-is-iso-pointed-map H))

  equiv-is-iso-is-equiv-pointed-map : is-equiv-pointed-map ≃ is-iso-pointed-map
  equiv-is-iso-is-equiv-pointed-map =
    pair
      ( is-iso-is-equiv-pointed-map)
      ( is-equiv-is-prop
        ( is-subtype-is-equiv (map-pointed-map A B f))
        ( is-prop-is-iso-pointed-map)
        ( is-equiv-is-iso-pointed-map))

_≃*_ :
  {l1 l2 : Level} (A : Pointed-Type l1) (B : Pointed-Type l2) → UU (l1 ⊔ l2)
A ≃* B =
  Σ ( type-Pointed-Type A ≃ type-Pointed-Type B)
    ( λ e → Id (map-equiv e (pt-Pointed-Type A)) (pt-Pointed-Type B))

compute-pointed-equiv :
  {l1 l2 : Level} (A : Pointed-Type l1) (B : Pointed-Type l2) →
  (A ≃* B) ≃ Σ (A →* B) (is-equiv-pointed-map A B)
compute-pointed-equiv A B = equiv-right-swap-Σ

module _
  {l1 l2 : Level} (A : Pointed-Type l1) (B : Pointed-Type l2) (e : A ≃* B)
  where

  equiv-pointed-equiv : type-Pointed-Type A ≃ type-Pointed-Type B
  equiv-pointed-equiv = pr1 e

  map-equiv-pointed-equiv : type-Pointed-Type A → type-Pointed-Type B
  map-equiv-pointed-equiv = map-equiv equiv-pointed-equiv

  preserves-point-equiv-pointed-equiv :
    Id (map-equiv-pointed-equiv (pt-Pointed-Type A)) (pt-Pointed-Type B)
  preserves-point-equiv-pointed-equiv = pr2 e

  pointed-map-pointed-equiv : A →* B
  pointed-map-pointed-equiv =
    pair map-equiv-pointed-equiv preserves-point-equiv-pointed-equiv

-- We characterize the identity type of the universe of pointed types

module _
  {l1 : Level} (A : Pointed-Type l1)
  where
  
  id-pointed-equiv : A ≃* A
  id-pointed-equiv = pair equiv-id refl

  pointed-equiv-eq : (B : Pointed-Type l1) → Id A B → A ≃* B
  pointed-equiv-eq .A refl = id-pointed-equiv

  is-contr-total-pointed-equiv : is-contr (Σ (Pointed-Type l1) (λ B → A ≃* B))
  is-contr-total-pointed-equiv =
    is-contr-total-Eq-structure
      ( λ X x (e : type-Pointed-Type A ≃ X) →
        Id (map-equiv e (pt-Pointed-Type A)) x)
      ( is-contr-total-equiv (type-Pointed-Type A))
      ( pair (type-Pointed-Type A) equiv-id)
      ( is-contr-total-path (pt-Pointed-Type A))

  is-equiv-pointed-equiv-eq :
    (B : Pointed-Type l1) → is-equiv (pointed-equiv-eq B)
  is-equiv-pointed-equiv-eq =
    fundamental-theorem-id A
      ( id-pointed-equiv)
      ( is-contr-total-pointed-equiv)
      ( pointed-equiv-eq)

  equiv-pointed-equiv-eq :
    (B : Pointed-Type l1) → Id A B ≃ (A ≃* B)
  equiv-pointed-equiv-eq B =
    pair (pointed-equiv-eq B) (is-equiv-pointed-equiv-eq B)

  eq-pointed-equiv : (B : Pointed-Type l1) → A ≃* B → Id A B
  eq-pointed-equiv B =
    map-inv-is-equiv (is-equiv-pointed-equiv-eq B)

-- Loop spaces

module _
  {l : Level} (A : Pointed-Type l)
  where
  
  type-Ω : UU l
  type-Ω = Id (pt-Pointed-Type A) (pt-Pointed-Type A)

  refl-Ω : type-Ω
  refl-Ω = refl

  Ω : Pointed-Type l
  Ω = pair type-Ω refl-Ω

-- Iterated loop spaces

module _
  {l : Level}
  where

  iterated-loop-space : ℕ → Pointed-Type l → Pointed-Type l
  iterated-loop-space zero-ℕ A = A
  iterated-loop-space (succ-ℕ n) A = Ω (iterated-loop-space n A)
  
  Ω² : Pointed-Type l → Pointed-Type l
  Ω² A = iterated-loop-space two-ℕ A
  
  type-Ω² : {A : UU l} (a : A) → UU l
  type-Ω² a = Id (refl {x = a}) (refl {x = a})
  
  refl-Ω² : {A : UU l} {a : A} → type-Ω² a
  refl-Ω² = refl
  
  Ω³ : Pointed-Type l → Pointed-Type l
  Ω³ A = iterated-loop-space three-ℕ A
  
  type-Ω³ : {A : UU l} (a : A) → UU l
  type-Ω³ a = Id (refl-Ω² {a = a}) (refl-Ω² {a = a})
  
  refl-Ω³ : {A : UU l} {a : A} → type-Ω³ a
  refl-Ω³ = refl

-- We compute transport of type-Ω

module _
  {l1 : Level} {A : UU l1} {x y : A} (p : Id x y)
  where

  equiv-tr-type-Ω : type-Ω (pair A x) ≃ type-Ω (pair A y)
  equiv-tr-type-Ω  = equiv-concat (inv p) y ∘e equiv-concat' x p

  tr-type-Ω : type-Ω (pair A x) → type-Ω (pair A y)
  tr-type-Ω = map-equiv equiv-tr-type-Ω

  is-equiv-tr-type-Ω : is-equiv tr-type-Ω
  is-equiv-tr-type-Ω = is-equiv-map-equiv equiv-tr-type-Ω

  preserves-point-tr-Ω : Id (tr-type-Ω refl) refl
  preserves-point-tr-Ω = left-inv p

  equiv-tr-Ω : Ω (pair A x) ≃* Ω (pair A y)
  equiv-tr-Ω = pair equiv-tr-type-Ω preserves-point-tr-Ω

-- We show that Ω is a functor

module _
  {l1 l2 : Level} (A : Pointed-Type l1) (B : Pointed-Type l2) (f : A →* B)
  where

  map-Ω : type-Ω A → type-Ω B
  map-Ω p =
    tr-type-Ω
      ( preserves-point-map-pointed-map A B f)
      ( ap (map-pointed-map A B f) p)
  
  preserves-refl-map-Ω : Id (map-Ω refl) refl
  preserves-refl-map-Ω = left-inv (preserves-point-map-pointed-map A B f)

  pointed-map-Ω : Ω A →* Ω B
  pointed-map-Ω = pair map-Ω preserves-refl-map-Ω


