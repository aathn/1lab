open import Cat.Functor.Subcategory
open import Cat.Prelude

open import Order.Instances.Pointwise
open import Order.Diagram.Lub
open import Order.Subposet
open import Order.Base
open import Order.DCPO

module Order.DCPO.Exponentials where

private variable
  o ℓ : Level

open is-directed-family
open is-dcpo
open is-lub
open Lub

Scott-maps : (A B : Poset o ℓ) → Poset (o ⊔ ℓ) (o ⊔ ℓ)
Scott-maps A B =
  Subposet Poset[ A , B ] λ f → el! (□ (is-scott-continuous f))

Scott-map : (A B : Poset o ℓ) → Type (o ⊔ ℓ)
Scott-map A B = ⌞ Scott-maps A B ⌟

pointwise-fam
  : {A B : Poset o o}
  → ∀ {Ix} (f : Ix → Scott-map A B) (f-fam : is-directed-family (Scott-maps A B) f)
  → ∀ x → is-directed-family B λ i → f i · x
pointwise-fam f f-fam _ .elt              = f-fam .elt
pointwise-fam f f-fam x .semidirected i j =
  ∥-∥-map (λ (k , i≤k , j≤k) → (k , i≤k x , j≤k x)) (f-fam .semidirected i j)


module _ (A B : DCPO o o) where
  private
    module A = DCPO A
    module B = DCPO B
    S = Scott-maps A.poset B.poset

  module _ {Ix} (f : Ix → Poset.Ob S) (f-fam : is-directed-family S f) where

    pointwise-lub : Monotone A.poset B.poset
    pointwise-lub .hom x    = B.⋃.lub _ (pointwise-fam f f-fam x)
    pointwise-lub .pres-≤ p = B.⋃-pointwise λ i → f i .fst .pres-≤ p
 
    pointwise-lub-is-scott : is-scott-continuous pointwise-lub
    pointwise-lub-is-scott s fam x x-lub .fam≤lub j =
      B.⋃-pointwise λ i → f i .fst .pres-≤ (x-lub .fam≤lub j)
    pointwise-lub-is-scott s fam x x-lub .least y y-ub = B.⋃.least _ _ _ λ i →
      f i · x                                         B.=⟨ lub-unique (□-out! (f i .snd) _ fam _ x-lub) (B.⋃.has-lub _ _) ⟩
      B.⋃.lub _ (monotone∘directed (f i .fst) fam)    B.≤⟨ B.⋃-pointwise (λ _ → B.fam≤⋃ _ _ i) ⟩
      B.⋃.lub _ (monotone∘directed pointwise-lub fam) B.≤⟨ B.⋃.least _ _ y y-ub ⟩
      y                                               B.≤∎

  Scott-maps-is-dcpo : is-dcpo S
  Scott-maps-is-dcpo .directed-lubs f f-fam .lub =
    pointwise-lub f f-fam , inc (pointwise-lub-is-scott f f-fam)
  Scott-maps-is-dcpo .directed-lubs f f-fam .has-lub = record where
    fam≤lub i x    = B.⋃.fam≤lub _ _ _
    least g g-ub x = B.⋃.least _ _ _ λ i → g-ub i x

  DCPO[_,_] : DCPO o o
  DCPO[_,_] = S , Scott-maps-is-dcpo
