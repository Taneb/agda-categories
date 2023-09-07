{-# OPTIONS --safe --without-K #-}

open import Categories.Category

module Categories.Functor.Slice.BaseChange {o ℓ e} (C : Category o ℓ e) {A B} (f : C [ B , A ]) where

open import Categories.Adjoint
open import Categories.Adjoint.Compose
open import Categories.Category.Equivalence.Properties
open import Categories.Category.Slice C
open import Categories.Category.Slice.Properties C
open import Categories.Diagram.Pullback C
open import Categories.Functor
open import Categories.Functor.Slice (Slice A)

open Category C

Σ : Functor (Slice B) (Slice A)
Σ = Sigma ∘F slice⇒slice-slice f

module _ (pullbacks : ∀ {X} {g : X ⇒ A} → Pullback f g) where

  Δ : Functor (Slice A) (Slice B)
  Δ = slice-slice⇒slice f ∘F Delta (pullback⇒product pullbacks)

  Σ⊣Δ : Σ ⊣ Δ
  Σ⊣Δ = C≅D.L⊣R (slice-slice≃slice f) ∘⊣ Sigma⊣Delta (pullback⇒product pullbacks)


