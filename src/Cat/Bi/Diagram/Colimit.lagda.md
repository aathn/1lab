<!--
```agda
open import Cat.Bi.Lax-functor.IndexedCategory
open import Cat.Bi.Lax-functor.Modification
open import Cat.Bi.Instances.Lax-functor
open import Cat.Bi.Lax-functor.Constant
open import Cat.Bi.Instances.Discrete
open import Cat.Bi.Lax-functor.Base
open import Cat.Functor.Equivalence
open import Cat.Bi.Lax-functor.Hom
open import Cat.Functor.Naturality
open import Cat.Functor.Bifunctor
open import Cat.Functor.Coherence
open import Cat.Displayed.Total
open import Cat.Functor.Adjoint
open import Cat.Bi.Equivalence hiding (is-equivalence)
open import Cat.Functor.Base
open import Cat.Bi.Duality hiding (_^op)
open import Cat.Bi.Solver
open import Cat.Bi.Base
open import Cat.Prelude

import Cat.Displayed.Reasoning as Dr
import Cat.Functor.Reasoning as Fr
import Cat.Bi.Reasoning as Br
import Cat.Reasoning as Cr
```
-->

```agda
module Cat.Bi.Diagram.Colimit where
```

# Bicategorical colimits

<!--
```agda
private variable
  o h ℓ o' h' ℓ' : Level

module _
  {I : Prebicategory o h ℓ}
  {C : Prebicategory o' (o ⊔ h ⊔ ℓ ⊔ h' ⊔ ℓ') (o ⊔ h ⊔ ℓ ⊔ ℓ')}
  (F : Pseudofunctor I C)
  where

  open Prebicategory C
  open Pseudofunctor
  open Pseudonatural
  open Lax-transfor
  open Modification
  open Cr.Inverses
  open Cr._≅_
  open _=>_
```
-->

[[Colimits]] are ubiquitous in category theory, describing universal
constructions of a certain form.  The same is true in bicategory theory,
where we can consider diagrams given by pseudofunctors $F : \bicat{I}
\to \bicat{C}$, and colimiting objects $L \in \bicat{C}$ such that any
cocone over $F$ with apex $X$ corresponds to an essentially unique
morphism $L \to X$.

The primary difference in dealing with bicategorical colimits compared
to their 1-categorical counterparts is that commutativity requirements
are relaxed to 2-cell isomorphisms.  Bicategorical colimits are also
more expressive in that the diagram can specify whether commutativity
conditions should hold up to isomorphism or merely a directed
transformation. For example, in a 1-category, given two parallel
morphisms

~~~{.quiver}
\[\begin{tikzcd}
  A & B
  \arrow["f", shift left=1, from=1-1, to=1-2]
  \arrow["g"', shift right=1, from=1-1, to=1-2]
\end{tikzcd}\]
~~~

we can consider a [[coequalizer]], i.e., a universal morphism $h : B \to
C$ identifying $f$ and $g$ in the sense that $h f = h g$.  In a
bicategory we can consider a directed version of this construction, the
coinserter, which consists of a universal 1-cell $h : B \to C$ equipped
with a 2-cell $h f \To h g$.

Other prominent examples of bicategorical colimits include, e.g, cocomma
categories, [[localisations]], and [[Kleisli categories]].

## Bicolimits and lax colimits {defines="bicolimit lax-colimit"}

To avoid having to define the machinery of cones or Kan extensions at
the level of bicategories, we use the characterisation of colimits as
[representing objects].  In 1-category theory, a functor $G : \ca{I} \to
\ca{C}$ has a colimit $L$ if and only if there is an isomorphism
$\ca{C}(L,X) \cong \thecat{Nat}(G,\Delta_X)$ natural in $X$.  Similarly,
in the setting of bicategories, we say that a pseudofunctor $F :
\bicat{I} \to \bicat{C}$ has a **bicolimit** $L$ if and only if there is
an equivalence of categories $\bicat{C}(L,X) \cong
\thebicat{Pseudo}(F,\Delta_X)$ pseudonatural in $X$, where
$\bicat{C}(L,-) : \bicat{C} \to \Cat$ is the [[bicategorical Hom
functor]], $\Delta_X$ is the [[constant pseudofunctor]] at $X$, and
$\thebicat{Pseudo}$ is the bicategory of pseudofunctors from $\bicat{I}$
to $\bicat{C}$.

[representing objects]: Cat.Diagram.Colimit.Representable.html

Recall that a natural transformation $\alpha : G \To \Delta_X$ specifies
a cocone over the functor $G$.  In the same way, a pseudonatural
transformation $\phi : F \To \Delta_X$ specifies a cocone over the
pseudofunctor $F$, illustrated in the diagram below.

~~~{.quiver}
\[\begin{tikzcd}[column sep=2.25em]
	& X \\
	{F(i)} & {F(j)}
	\arrow[""{name=0, anchor=center, inner sep=0}, "{\phi_i}", from=2-1, to=1-2]
	\arrow["{F(f)}"', from=2-1, to=2-2]
	\arrow["{\phi_j}"', from=2-2, to=1-2]
	\arrow["{\nu_{i,j}}", between={0.2}{1}, "{\sim}", Rightarrow, from=0, to=2-2]
\end{tikzcd}\]
~~~

For each object $i$ in the diagram, $\phi_i : F(i) \to X$ gives a leg of
the cocone, and for any morphism $f : i \to j$, we have a 2-cell
isomorphism $\nu_{i,j} : \phi_i \cong \phi_j F(f)$ in place of the usual
commutativity requirement for cocones.

As is often the case in bicategorical definitions, we have the choice of
whether to consider cocones $F \to \Delta_X$ which commute strongly (so
that $\nu_{i,j}$ is an isomorphism as above), or to take cocones with
"directed" commutative squares (so that $\nu_{i,j}$ is a general
2-cell).  The latter choice yields the notion of a **lax colimit** (or
oplax, depending on the direction of the 2-cells).  It is known that
(op-)lax colimits can be expressed as bicolimits by altering the diagram
category, but in this page, we mainly deal with lax colimits, so we opt
to define those directly.

## Defining lax colimits

A lax colimit of a pseudofunctor $F : \bicat{I} \to \bicat{C}$ consists
of an object $L$ in $\bicat{C}$ together with a pseudonatural
equivalence $\bicat{C}(L,-) \cong \thebicat{Pseudo}_o(F,\Delta)$,
where $\thebicat{Pseudo}_$ denotes the bicategory of pseudofunctors from
$\bicat{I}$ to $\bicat{C}$ together with *oplax* transformations between
them.[^why-oplax]  The codomain of this equivalence can be translated
into Agda as follows.

[^why-oplax]: The reason that the lax colimit involves oplax
transformations is that a lax colimit is defined to coincide with a lax
limit in the opposite bicategory, which ends up reversing the direction
of cocone 2-cells.

```agda
  lax-cocones-at : Pseudofunctor C (Cat _ _)
  lax-cocones-at = Hom-from-bi (Pseudoₒ I C) (opᵖ F) P∘ Const-pseudoₒ
```

Now, by a bicategorical Yoneda argument, any pseudonatural equivalence
of the form discussed is determined by its value at $\id : L \to L$,
which is a cocone $F \To \Delta_L$, namely the universal colimiting
cocone.

Under the Yoneda correspondence, a cocone at $L$ induces a functor
$\bicat{C}(L,X) \to \thebicat{Pseudo}_o(F,\Delta_L)$ by precomposition.

```agda
  module _ {L : Ob} (univ-cocone : opᵖ F .lax =>ₒ ConstP L .lax) where

    hom→cocone₀ : (X : Ob) → Functor (Hom L X) Pseudoₒ[ opᵖ F , ConstP X ]
    hom→cocone₀ X =
         preaction (Pseudoₒ _ _) {opᵖ F} {ConstP L} {ConstP X} univ-cocone
      F∘ Const-pseudoₒ.Const₁
```

<details>
<summary>
We can show that `hom→cocone₀`{.Agda} extends to a pseudonatural
transformation without too much effort.  We elide the details, which
mostly boil down to automated bicategory reasoning.
</summary>
```agda
    module _ {X Y : Ob} where
      hom→cocone-nat
        :  preaction (Cat _ _) (hom→cocone₀ Y)
        F∘ Flip (Lax.compose _ _) F∘ Const-pseudoₒ.Const₁
        ≅ⁿ postaction (Cat _ _) (hom→cocone₀ X) F∘ compose
      hom→cocone-nat = to-natural-iso ni where
        ni : make-natural-iso _ _
        ni .make-natural-iso.eta f .η g .Γ a         = α← _
        ni .make-natural-iso.eta f .η g .is-natural  = bicat! C
        ni .make-natural-iso.eta f .is-natural g h α = ext λ _ → bicat! C
        ni .make-natural-iso.inv f .η g .Γ a         = α→ _
        ni .make-natural-iso.inv f .η g .is-natural  = bicat! C
        ni .make-natural-iso.inv f .is-natural g h α = ext λ _ → bicat! C
        ni .make-natural-iso.eta∘inv f               = ext λ _ _ → Br.α≅ C .invr
        ni .make-natural-iso.inv∘eta f               = ext λ _ _ → Br.α≅ C .invl
        ni .make-natural-iso.natural g h α           = ext λ _ _ → bicat! C

    hom→cocone : Hom-from-bi C L .lax =>ₚ lax-cocones-at .lax
    hom→cocone .lax .σ                = hom→cocone₀
    hom→cocone .lax .naturator        = hom→cocone-nat .to
    hom→cocone .lax .ν-compositor f g = ext λ _ _ → bicat! C
    hom→cocone .lax .ν-unitor         = ext λ _ _ → bicat! C
    hom→cocone .naturator-inv f       =
      Cr.iso→invertible Cat[ _ , _ ] (isoⁿ→iso hom→cocone-nat f)
```

In other words, to show that $L$ is the lax colimit of $F$, it suffices
to provide a candidate cocone with apex $L$, and show that
`hom→cocone`{.Agda} is a pseudonatural equivalence, which corresponds to
showing that the provided cocone is universal.

```agda
    is-lax-colimit : Type _
    is-lax-colimit = is-equivalenceᵖ hom→cocone
```

## Lax colimits of indexed categories

An especially important case of lax colimits are those of [[indexed
categories]], i.e., contravariant pseudofunctors from a [[locally
discrete bicategory]] into $\Cat$.  For an indexed category $F : \ca{I}
\to \Cat$, the lax colimit of $F$ coincides with the [[Grothendieck
construction]] $\int F$, which is what we show in the remainder of this
module.

<!--
```agda
module IndexedCategoryLaxColim
  {I : Precategory o h}
  (F : Pseudofunctor (Locally-discrete (I ^op)) (Cat (o ⊔ o') (h ⊔ h')))
  where
  open Pseudofunctor
  open Lax-transfor
  open Modification
  open Cr.Inverses
  open Functor
  open Cr._≅_
  open _=>_

  private
    module I      = Precategory I
    module F      = IndexedCategory F
    module F₀ {x} = Cr (F.₀ x)
    module G      = Cr (∫ F.displayed)
    module Cat    = Br (Cat (o ⊔ o') (h ⊔ h'))

    open Dr F.displayed
```
-->

```agda
  univ-cocone : opᵖ F .lax =>ₒ ConstP F.∫ .lax
```

To construct the universal cocone, we use the canonical inclusion
functors from the fibre categories of $F$ into $\int F$.

```agda
  univ-cocone .σ a = F.ιᶠ a
```

The naturality 2-cells are straightforward to define, and we did so
already off-screen.

```agda
  univ-cocone .naturator .η f = nat-unidl-to (F.ιᶠ-base-change f)
```

<details>
<summary>
Verifying that this data satisfies the required naturality and
compatibility requirements is tedious but straightforward in principle,
so we elide the details.
</summary>
```agda
  univ-cocone .naturator .is-natural f g =
    J (λ g p → nat-unidl-to (F.ιᶠ-base-change g) ∘nt (_ ▸ F.₂ p)
             ≡ (idnt ◂ _) ∘nt nat-unidl-to (F.ιᶠ-base-change f)) $
    nat-unidl-to (F.ιᶠ-base-change f) ∘nt (_ ▸ F.₂ refl) ≡⟨ Cat.Hom.elimr (Fr.elim (postaction (Cat _ _) _) F.P₁.F-id) ⟩
    nat-unidl-to (F.ιᶠ-base-change f)                    ≡⟨ Cat.Hom.introl Cat.◀.F-id ⟩
    (idnt ◂ _) ∘nt nat-unidl-to (F.ιᶠ-base-change f)     ∎
  univ-cocone .ν-compositor f g = ext λ _ → sym $
    let
      p : id' ∘' id' ≡ (id' F₀.∘ F.γ← _ .η _) ∘' id' F₀.∘ F.γ→ _ .η _
      p = cast[] (idr' _ ∙[] F₀.insertr (F.γ≅' .invr) ∙[] symP F.cancel-id')
    in
       G.eliml (G.idl _) ∙ G.idl _
    ∙∙ G.cdr (G.idl _ ∙ G.cdr (sym (G.idr _) ∙ Fr.weave (ιᶠ _ _) (F₀.cdr p)))
    ∙∙ sym (G.pushl3 (F.ιᶠ-base-change-comp f g ηₚ _))
  univ-cocone .ν-unitor = ext λ _ →
    Fr.weave (ιᶠ _ _)
      (F₀.cdr (cast[] (F.cancel-id' ∙[] F₀.idl _ ∙[] symP (idr' _))))
    ∙ G.introl (G.idl _)
```
</details>

To show that this cocone is universal, we must show that for any other
lax cocone with apex $X$, we can construct a functor $\int F \to X$
which factors the other cocone through the universal one.

```agda
  module _ (X : Precategory (o ⊔ o') (h ⊔ h')) where
```

<!--
```agda
    open Cr X hiding (invl ; invr)
    private
      module Ox = IndexedOplax {F = opᵖ F} {ConstP X}
      ν-unitor'
        : ∀ (α : ⌞ Pseudoₒ[ opᵖ F , ConstP X ] ⌟ ) {i} y
        → α .ν→ I.id .η y ∘ α .σ i .F₁ (F.υ→ .η _) ≡ id
      ν-unitor' α y = Ox.ν-unitor α y ∙ idr _
```
-->

```agda
    cocone→mediator₀ : opᵖ F .lax =>ₒ ConstP X .lax → Functor F.∫ X
    cocone→mediator₀ α = funct where
```

Assume that we are given a lax cocone $\alpha : F \To \Delta_X$.  This
is an oplax transformation with functor components $F(i) \to X$ for each
$i \in \ca{I}$.  Since an object of $\int F$ bundles an $i \in \ca{I}$
with some $a \in F(i)$, we can use $\alpha_i$ to map $a$ into $X$,
giving us the object mapping we need.

```agda
      module α = Lax-transfor α
      funct : Functor F.∫ X
      funct .F₀ (x , Fx) = α.σ x .F₀ Fx
```

```agda
      funct .F₁ {x , Fx} {y , Fy} (∫hom f Ff) = α.ν→ f .η Fy ∘ α.σ x .F₁ Ff
      funct .F-id {x , Fx}                    = ν-unitor' α Fx
      funct .F-∘ {x , Fx} {y , Fy} {z , Fz} (∫hom f Ff) (∫hom g Fg) =
        α.ν→ (f I.∘ g) .η Fz ∘ α.σ x .F₁ (Ff ∘' Fg)                          ≡⟨ cdr (sym $ Fr.collapse3 (α.σ x) refl) ⟩
        α.ν→ (f I.∘ g) .η Fz ∘ α.σ x .F₁ (F.γ→ (g , f) .η Fz) ∘ _            ≡⟨ extendl (Ox.ν-compositor α f g Fz ∙ eliml (idl _)) ⟩
        α.ν→ f .η Fz ∘ α.ν→ g .η _ ∘ α.σ x .F₁ (F.₁ g .F₁ Ff) ∘ α.σ x .F₁ Fg ≡⟨ cdr (extendl (α.ν→ g .is-natural _ _ _)) ∙ assoc _ _ _ ⟩
        (α.ν→ f .η Fz ∘ α.σ y .F₁ Ff) ∘ α.ν→ g .η Fy ∘ α.σ x .F₁ Fg          ∎

    cocone→mediator : Functor Pseudoₒ[ opᵖ F , ConstP X ] Cat[ F.∫ , X ]
    cocone→mediator .F₀               = cocone→mediator₀
    cocone→mediator .F₁ γ .η (x , Fx) = γ .Γ x .η Fx
    cocone→mediator .F₁ {α} {β} γ .is-natural (x , Fx) (y , Fy) (∫hom f Ff) =
      γ .Γ y .η Fy ∘ α .ν→ f .η Fy ∘ α .σ x .F₁ Ff             ≡˘⟨ extendl (γ .is-natural ηₚ Fy) ⟩
      β .ν→ f .η Fy ∘ γ .Γ x .η (F.₁ f .F₀ Fy) ∘ α .σ x .F₁ Ff ≡⟨ pushr (γ .Γ x .is-natural _ _ _) ⟩
      (β .ν→ f .η Fy ∘ β .σ x .F₁ Ff) ∘ γ .Γ x .η Fx           ∎
    cocone→mediator .F-id    = ext λ _ → refl
    cocone→mediator .F-∘ γ δ = ext λ _ → refl

    private
      hom→cocone' = hom→cocone₀ {h' = lzero} {o' ⊔ h'} F univ-cocone X

    cocone→mediator-unit : Id ≅ⁿ hom→cocone' F∘ cocone→mediator
    cocone→mediator-unit = to-natural-iso ni where
      abstract
        cocone-factors
          : ∀ (α : ⌞ Pseudoₒ[ opᵖ F , ConstP X ] ⌟ ) {a b} {f : I.Hom b a} i
          → α .ν→ f .η i ≡ (hom→cocone' F∘ cocone→mediator) .F₀ α .ν→ f .η i
        cocone-factors α i =
          sym $ idl _ ∙∙ eliml (idl _) ∙∙ idl _ ∙∙ idr _ ∙∙ elimr (α .σ _ .F-id)

      ni : make-natural-iso _ _
      ni .make-natural-iso.eta α .Γ a .η _              = id
      ni .make-natural-iso.eta α .Γ a .is-natural _ _ _ =
        pushl (sym (ν-unitor' α _)) ∙∙ sym (cdr (α .σ a .F-∘ _ _)) ∙∙ sym (idr _)
      ni .make-natural-iso.eta α .is-natural = ext λ i →
        idr _ ∙∙ sym (cocone-factors α i) ∙∙ sym (idl _)
      ni .make-natural-iso.inv α .Γ a .η _              = id
      ni .make-natural-iso.inv α .Γ a .is-natural _ _ _ =
        idl _ ∙ cdr (α .σ a .F-∘ _ _) ∙∙ cancell (ν-unitor' α _) ∙∙ sym (idr _)
      ni .make-natural-iso.inv α .is-natural {b = b} = ext λ i →
        idr _ ∙∙ cocone-factors α i ∙∙ sym (idl _)
      ni .make-natural-iso.eta∘inv _     = ext λ _ _ → idl _
      ni .make-natural-iso.inv∘eta _     = ext λ _ _ → idl _
      ni .make-natural-iso.natural _ α f = ext λ _ _ → idr _ ∙ car (ν-unitor' α _)

    cocone→mediator-counit : cocone→mediator F∘ hom→cocone' ≅ⁿ Id
    cocone→mediator-counit = to-natural-iso ni where
      mediator-stable
        : ∀ (G : Functor F.∫ X) {a b} (f : G.Hom a b)
        → (cocone→mediator F∘ hom→cocone') .F₀ G .F₁ f ≡ G .F₁ f
      mediator-stable G (∫hom f Ff) =
          car (idl _ ∙ eliml (idl _) ∙∙ idl _ ∙∙ idr _)
        ∙ Fr.collapse G (∫Hom-path _ (I.idr _) $ cast[] $ F.cancel-id' ∙[] F₀.idl _)

      ni : make-natural-iso _ _
      ni .make-natural-iso.eta G .η _              = id
      ni .make-natural-iso.eta G .is-natural _ _ f =
        idl _ ∙∙ mediator-stable G f ∙∙ sym (idr _)
      ni .make-natural-iso.inv G .η _              = id
      ni .make-natural-iso.inv G .is-natural _ _ f =
        idl _ ∙∙ sym (mediator-stable G f) ∙∙ sym (idr _)
      ni .make-natural-iso.eta∘inv _ = ext λ _ → idl _
      ni .make-natural-iso.inv∘eta _ = ext λ _ → idl _
      ni .make-natural-iso.natural G H α = ext λ _ →
        idr _ ∙ introl (H .F-id) ∙ sym (idl _)

    cocone→mediator⊣ : cocone→mediator ⊣ hom→cocone'
    cocone→mediator⊣ ._⊣_.unit    = cocone→mediator-unit .to
    cocone→mediator⊣ ._⊣_.counit  = cocone→mediator-counit .to
    cocone→mediator⊣ ._⊣_.zig     = ext λ _   → idl _
    cocone→mediator⊣ ._⊣_.zag {G} = ext λ _ _ → idr _ ∙ eliml (G .F-id)

    cocone→mediator-equiv : is-equivalence cocone→mediator
    cocone→mediator-equiv .is-equivalence.F⁻¹        = hom→cocone'
    cocone→mediator-equiv .is-equivalence.F⊣F⁻¹      = cocone→mediator⊣
    cocone→mediator-equiv .is-equivalence.unit-iso α =
      Cr.iso→invertible Laxₒ[ _ , _ ] (isoⁿ→iso cocone→mediator-unit α)
    cocone→mediator-equiv .is-equivalence.counit-iso G =
      Cr.iso→invertible Cat[ _ , _ ] (isoⁿ→iso cocone→mediator-counit G)

  ∫-colim : is-lax-colimit {h' = lzero} {o' ⊔ h'} F univ-cocone
  ∫-colim X = is-equivalenceᶜ→is-equivalence
    $ is-equivalence.inverse-equivalence (cocone→mediator-equiv X)
```
