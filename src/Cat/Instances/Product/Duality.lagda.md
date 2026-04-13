<!--
```agda
open import Cat.Functor.Equivalence
open import Cat.Instances.Product
open import Cat.Functor.Adjoint
open import Cat.Prelude

import Cat.Reasoning as Cr
```
-->

```agda
module Cat.Instances.Product.Duality {o₁ h₁ o₂ h₂ : Level}
  {C : Precategory o₁ h₁} {D : Precategory o₂ h₂}
  where
```

<!--
```agda
open Functor
open _=>_
open is-equivalence
private
  module C = Precategory C
  module D = Precategory D
```
-->

# Duality of product categories {defines="opposite-product-category"}

As one might expect, taking the [[opposite category]] of a [[product category]]
agrees with the product of opposite categories. Rather than showing
equality we construct an [[equivalence of categories]].

```agda
×^op→ : Functor ((C ×ᶜ D)^op) (C ^op ×ᶜ D ^op)
×^op→ .F₀ x    = x
×^op→ .F₁ f    = f
×^op→ .F-id    = refl
×^op→ .F-∘ f g = refl

×^op← : Functor (C ^op ×ᶜ D ^op) ((C ×ᶜ D)^op)
×^op← .F₀ x    = x
×^op← .F₁ f    = f
×^op← .F-id    = refl
×^op← .F-∘ f g = refl
```

Since the objects and morphisms in the two categories agree
definitionally, constructing the equivalence is trivial.

```agda
×^op-is-equiv : is-equivalence ×^op→
×^op-is-equiv .F⁻¹                                 = ×^op←
×^op-is-equiv .F⊣F⁻¹ ._⊣_.unit .η x                = C.id , D.id
×^op-is-equiv .F⊣F⁻¹ ._⊣_.unit .is-natural _ _ f   = Cr.id-comm C ,ₚ Cr.id-comm D
×^op-is-equiv .F⊣F⁻¹ ._⊣_.counit .η x              = C.id , D.id
×^op-is-equiv .F⊣F⁻¹ ._⊣_.counit .is-natural _ _ f = Cr.id-comm C ,ₚ Cr.id-comm D
×^op-is-equiv .F⊣F⁻¹ ._⊣_.zig                      = C.idr _ ,ₚ D.idr _
×^op-is-equiv .F⊣F⁻¹ ._⊣_.zag                      = C.idr _ ,ₚ D.idr _
×^op-is-equiv .unit-iso _                          = Cr.id-invertible _
×^op-is-equiv .counit-iso _                        = Cr.id-invertible _
```

