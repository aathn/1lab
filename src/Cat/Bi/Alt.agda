open import Cat.Functor.Naturality
open import Cat.Functor.Bifunctor
open import Cat.Instances.Product
open import Cat.Functor.Coherence renaming (_◆_ to _◇_)
open import Cat.Functor.Closed
open import Cat.Functor.Base
open import Cat.Prelude

import Cat.Functor.Reasoning as Fr
import Cat.Reasoning as Cr

module Cat.Bi.Alt where

record Raw-prebicategory o h ℓ : Type (lsuc (o ⊔ h ⊔ ℓ)) where
  no-eta-equality
  field
    Ob  : Type o
    Hom : Ob → Ob → Precategory h ℓ

  module Hom {A} {B} = Precategory (Hom A B) hiding (Ob ; Hom ; _∘_)

  field
    id      : ∀ {A} → ⌞ Hom A A ⌟
    compose : ∀ {A B C} → Bifunctor (Hom B C) (Hom A B) (Hom A C)

  module compose {a b c} = Bifunctor (compose {a} {b} {c}) hiding (_◀_ ; _▶_ ; F₀)
  private
    open module ↦ A B = Precategory (Hom A B)
      public using () renaming (Ob to _↦_)

    open module Hom₁ {A B} = Precategory (Hom A B)
      public using () renaming (Hom to _⇒_ ; _∘_ to infixr 30 _∘_)

    open module compose₀ {A B C} = Bifunctor (compose {A} {B} {C})
      public using (_◀_ ; _▶_ ; _◆_) renaming (F₀ to infixr 25 _⊗_)

module Free-hom {o h ℓ} (B : Raw-prebicategory o h ℓ) where
  open Raw-prebicategory B
  private
    variable
      W X Y Z : Ob
    module CH {A} {B} = Cr (Hom A B)

  data Expr₁ : Ob → Ob → Type (o ⊔ h) where
    _↑   : X ↦ Y → Expr₁ X Y
    `id  : Expr₁ X X
    _`⊗_ : Expr₁ Y Z → Expr₁ X Y → Expr₁ X Z

  infix  50 _↑
  infixr 30 _`⊗_

  ⟦_⟧₁ : Expr₁ X Y → X ↦ Y
  ⟦_⟧₁ (x ↑)    = x
  ⟦_⟧₁ `id      = id
  ⟦_⟧₁ (f `⊗ g) = ⟦ f ⟧₁ ⊗ ⟦ g ⟧₁

  data Expr₂ : Expr₁ X Y → Expr₁ X Y → Type (o ⊔ h ⊔ ℓ) where
    _↑   : {f g : Expr₁ X Y} → ⟦ f ⟧₁ ⇒ ⟦ g ⟧₁ → Expr₂ f g
    `id  : {f : Expr₁ X Y} → Expr₂ f f
    _`∘_ : {f g h : Expr₁ X Y} → Expr₂ g h → Expr₂ f g → Expr₂ f h
    _`▶_
      : (f : Expr₁ Y Z) {g₁ g₂ : Expr₁ X Y} → Expr₂ g₁ g₂ → Expr₂ (f `⊗ g₁) (f `⊗ g₂)
    _`◀_
      : {f₁ f₂ : Expr₁ Y Z} → Expr₂ f₁ f₂ → (g : Expr₁ X Y) → Expr₂ (f₁ `⊗ g) (f₂ `⊗ g)

  infixr 40 _`∘_
  infix 40 _`▶_
  infix 40 _`◀_

  ⟦_⟧₂ : {f g : Expr₁ X Y} → Expr₂ f g → ⟦ f ⟧₁ ⇒ ⟦ g ⟧₁
  ⟦ x ↑ ⟧₂     = x
  ⟦ `id ⟧₂     = Hom.id
  ⟦ x `∘ x₁ ⟧₂ = ⟦ x ⟧₂ ∘ ⟦ x₁ ⟧₂
  ⟦ f `▶ x ⟧₂  = ⟦ f ⟧₁ ▶ ⟦ x ⟧₂
  ⟦ x `◀ g ⟧₂  = ⟦ x ⟧₂ ◀ ⟦ g ⟧₁

  eval₁ : Expr₁ X Y → Z ↦ X → Z ↦ Y
  eval₁ (x ↑)    = x ⊗_
  eval₁ `id      = λ k → k
  eval₁ (f `⊗ g) = eval₁ f ⊙ eval₁ g

  nf₁ : Expr₁ X Y → X ↦ Y
  nf₁ (x ↑)    = x
  nf₁ `id      = id
  nf₁ (f `⊗ g) = eval₁ f (nf₁ g)

  `whisker
    : (f : Expr₁ Y Z) {h₁ h₂ : X ↦ Y} → h₁ ⇒ h₂
    → eval₁ f h₁ ⇒ eval₁ f h₂
  `whisker (x ↑) α       = x ▶ α
  `whisker `id α         = α
  `whisker (_`⊗_ f f₁) α = `whisker f (`whisker f₁ α)

  module _ (cohere : ∀ {A B} (f : Expr₁ A B) → nf₁ f CH.≅ ⟦ f ⟧₁) where

    private module cohere {A B} (f : Expr₁ A B) = CH._≅_ (cohere f)

    eval₂ : {a b : Expr₁ Y Z} → Expr₂ a b → {k : X ↦ Y} → eval₁ a k ⇒ eval₁ b k
    eval₂ {a = a} {b} (x ↑) {k} =
      cohere.from (b `⊗ k ↑) ∘ x ◀ k ∘ cohere.to (a `⊗ k ↑)
    eval₂ `id       = Hom.id
    eval₂ (α `∘ α₁) = eval₂ α ∘ eval₂ α₁
    eval₂ (f `▶ α)  = `whisker f (eval₂ α)
    eval₂ (α `◀ g)  = eval₂ α

    nf₂ : {a b : Expr₁ Y Z} → Expr₂ a b → nf₁ a ⇒ nf₁ b
    nf₂ {a = a} {b} (x ↑) = cohere.from b ∘ x ∘ cohere.to a
    nf₂ `id               = Hom.id
    nf₂ (α `∘ β)          = nf₂ α ∘ nf₂ β
    nf₂ (f `▶ α)          = `whisker f (nf₂ α)
    nf₂ (α `◀ g)          = eval₂ α

record Prebicategory o h ℓ : Type (lsuc (o ⊔ h ⊔ ℓ)) where
  no-eta-equality
  field
    raw-pb : Raw-prebicategory o h ℓ

  open Raw-prebicategory raw-pb public
  open Free-hom raw-pb
  private module CH {A} {B} = Cr (Hom A B)

  field
    cohere : ∀ {A B} (f : Expr₁ A B) → nf₁ f CH.≅ ⟦ f ⟧₁

  module cohere {A B} (f : Expr₁ A B) = CH._≅_ (cohere f)

  field
    cohere-nat
      : ∀ {A B} {f f' : Expr₁ A B} (α : Expr₂ f f')
      → ⟦ α ⟧₂ ∘ cohere.to f ≡ cohere.to f' ∘ nf₂ cohere α

    cohere-id : ∀ {A} → cohere.to (`id {A}) ≡ Hom.id

    cohere-⊗
      : ∀ {A B C} {f f' : Expr₁ B C} {g g' : Expr₁ A B}
      → cohere.to (f `⊗ g) ≡ ⟦ f ⟧₁ ▶ cohere.to g ∘ cohere.to (f `⊗ nf₁ g ↑)

private module Pb = Prebicategory

Cat : ∀ o ℓ → Prebicategory (lsuc o ⊔ lsuc ℓ) (o ⊔ ℓ) (o ⊔ ℓ)
Cat o ℓ = pb where
  open Functor

  -- assoc : Associator-for Cat[_,_] F∘-functor
  -- assoc {C = C} {D = D} = to-natural-iso ni where
  --   module D = Cr D using (id ; idl ; idr ; pushr ; introl ; id-comm-sym)
  --   ni : make-natural-iso {D = Cat[ _ , _ ]} _ _
  --   ni .make-natural-iso.eta x = NT (λ _ → D.id) λ _ _ _ → D.id-comm-sym
  --   ni .make-natural-iso.inv x = NT (λ _ → D.id) λ _ _ _ → D.id-comm-sym
  --   ni .make-natural-iso.eta∘inv x = ext λ _ → D.idl _
  --   ni .make-natural-iso.inv∘eta x = ext λ _ → D.idl _
  --   ni .make-natural-iso.natural (X₀ , X₁ , X₂) _ _ = ext λ _ →
  --     D.idr _ ∙∙ D.pushr (X₀ .F-∘ _ _) ∙∙ D.introl refl
  raw : Raw-prebicategory _ _ _
  raw .Raw-prebicategory.Ob      = Precategory o ℓ
  raw .Raw-prebicategory.Hom     = Cat[_,_]
  raw .Raw-prebicategory.id      = Id
  raw .Raw-prebicategory.compose = F∘-functor

  open Raw-prebicategory raw
  open Free-hom raw

  cohere' : ∀ {A B C : Ob} (f : Expr₁ A B) {k : C ↦ A} → eval₁ f k => ⟦ f ⟧₁ F∘ k
  cohere' (x ↑)     = idnt
  cohere' `id       = nat-unidl-to idnt
  cohere' (f `⊗ f₁) = nat-assoc-to (⟦ f ⟧₁ ▶ cohere' f₁ ∘ cohere' f)

  -- cohere'
  --   : ∀ {A B C : Ob} (f : Expr₁ A B) {k : C ↦ A}
  --   → Cr._≅_ Cat[ _ , _ ] (eval₁ f k) (⟦ f ⟧₁ F∘ k)
  -- cohere' (x ↑)       = Cr.id-iso _
  -- cohere' {A = A} `id = to-natural-iso ni where
  --   module A = Cr A using (id ; idl ; idr ; id-comm)
  --   ni : make-natural-iso _ _
  --   ni .make-natural-iso.eta x = A.id
  --   ni .make-natural-iso.inv x = A.id
  --   ni .make-natural-iso.eta∘inv x = A.idr _
  --   ni .make-natural-iso.inv∘eta x = A.idr _
  --   ni .make-natural-iso.natural _ _ f = A.id-comm
  -- cohere' (f `⊗ f₁) = to-natural-iso ni where
  --   module cohere' {A B C : Ob} (f : Expr₁ A B) {k : C ↦ A} =
  --     Cr._≅_ Cat[ _ , _ ] (cohere' f {k})
  --   ni : make-natural-iso _ _
  --   ni .make-natural-iso.eta x = {!!}
  --   ni .make-natural-iso.inv x = {!!}
  --   ni .make-natural-iso.eta∘inv x = {!!}
  --   ni .make-natural-iso.inv∘eta x = {!!}
  --   ni .make-natural-iso.natural = {!!}

  pb : Prebicategory _ _ _
  pb .Pb.raw-pb           = raw
  pb .Pb.cohere (x ↑)     = Cr.id-iso _
  pb .Pb.cohere `id       = Cr.id-iso _
  pb .Pb.cohere (f `⊗ f₁) = {!!}
  pb .Pb.cohere-nat = {!!}
  pb .Pb.cohere-id = {!!}
  pb .Pb.cohere-⊗ = {!!}
  -- pb .Ob = Precategory o ℓ
  -- pb .Hom = Cat[_,_]
  -- pb .id = Id

  -- pb .compose = F∘-functor

  -- pb .unitor-r {B = B} = to-natural-iso ni where
  --   module B = Cr B using (id ; _∘_ ; idl ; idr ; id-comm-sym ; id-comm)
  --   ni : make-natural-iso {D = Cat[ _ , _ ]} _ _
  --   ni .make-natural-iso.eta x = NT (λ _ → B.id) λ _ _ _ → B.id-comm-sym
  --   ni .make-natural-iso.inv x = NT (λ _ → B.id) λ _ _ _ → B.id-comm-sym
  --   ni .make-natural-iso.eta∘inv x = ext λ _ → B.idl _
  --   ni .make-natural-iso.inv∘eta x = ext λ _ → B.idl _
  --   ni .make-natural-iso.natural x y f = ext λ _ → B.id-comm

  -- pb .unitor-l {B = B} = to-natural-iso ni where
  --   module B = Cr B using (id ; idl ; idr ; id-comm ; id-comm-sym)
  --   ni : make-natural-iso {D = Cat[ _ , _ ]} _ _
  --   ni .make-natural-iso.eta x = NT (λ _ → B.id) λ _ _ _ → B.id-comm-sym
  --   ni .make-natural-iso.inv x = NT (λ _ → B.id) λ _ _ _ → B.id-comm-sym
  --   ni .make-natural-iso.eta∘inv x = ext λ _ → B.idl _
  --   ni .make-natural-iso.inv∘eta x = ext λ _ → B.idl _
  --   ni .make-natural-iso.natural x y f = ext λ _ → B.id-comm

  -- pb .associator = assoc

  -- pb .triangle {C = C} f g = ext λ _ → C .Cr.idl _ ∙ sym (f .F-id)
  -- pb .pentagon {E = E} f g h i = ext λ _ → ap₂ E._∘_ refl (E.elimr (f .F-id))
  --   where module E = Cr E using (_∘_ ; elimr)
