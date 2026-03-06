{-# OPTIONS --without-K --safe #-}

module Categories.Bicategory.Instance.DagCats where

open import Categories.Bicategory using (Bicategory)
open import Categories.Category.Construction.DaggerFunctors using (DaggerFunctors; product; product-assoc)
open import Categories.Category.Dagger using (DaggerCategory)
open import Categories.Functor.Construction.Constant using (const)
open import Categories.Functor.Dagger using (DaggerFunctor; _∘F†_) renaming (id to idF†)

import Categories.Morphism.Reasoning as MR
open import Categories.NaturalTransformation using (NaturalTransformation; ntHelper; F∘id⇒F; F⇒F∘id)
open import Categories.NaturalTransformation.NaturalIsomorphism using (niHelper; unitorʳ)

open import Data.Product.Base using (_,_)

open import Level using (Level; suc; _⊔_)

DagCats : (o ℓ e : Level) → Bicategory (o ⊔ ℓ ⊔ e) (o ⊔ ℓ ⊔ e) (o ⊔ e) (suc (o ⊔ ℓ ⊔ e))
DagCats o ℓ e = record
  { enriched = record
    { Obj = DaggerCategory o ℓ e
    ; hom = DaggerFunctors
    ; id = const idF†
    ; ⊚ = product
    ; ⊚-assoc = {!product-assoc!}
    ; unitˡ = λ {A B} → let
      open DaggerCategory B
      open MR C
      in niHelper record
      { η = λ (_ , F) → ntHelper record
        { η = λ _ → id
        ; commute = λ _ → id-comm-sym
        }
      ; η⁻¹ = λ (_ , F) → ntHelper record
        { η = λ _ → id
        ; commute = λ _ → id-comm-sym
        }
      ; commute = λ _ → identityˡ
      ; iso = λ (_ , F) → record
        { isoˡ = identity²
        ; isoʳ = identity²
        }
      }
    ; unitʳ = λ {_ B} → let
      open DaggerCategory B
      open MR C
      open HomReasoning
      in niHelper record
        { η = λ (F , _) → F∘id⇒F
        ; η⁻¹ = λ (_ , F) → F⇒F∘id
        ; commute = λ {_} {(F , _)} _ → identityˡ ○ elimˡ (identity F) ○ Equiv.sym identityʳ
        ; iso = λ (F , _) → record
          { isoˡ = identity²
          ; isoʳ = identity²
          }
        }
    }
  ; triangle = λ {_ _ C F G x} →
    let open DaggerCategory C
    in ∘-resp-≈ˡ identityʳ
  ; pentagon = λ {A B C D E} {F G H I} {X} →
    let
      open DaggerCategory E renaming (C to U)
      open MR U
      open HomReasoning
      module B = DaggerCategory B
      module D = DaggerCategory D
    in begin
      (F₁ I D.id ∘ id) ∘ (id ∘ F₁ I (F₁ H (F₁ G B.id)) ∘ id) ≈⟨ identity I ⟩∘⟨refl ⟩∘⟨ refl⟩∘⟨ identity (I ∘F† H ∘F† G) ⟩∘⟨refl ⟩
      (id ∘ id) ∘ (id ∘ id ∘ id)                             ≈⟨ identity² ⟩∘⟨ cancelˡ identity² ⟩
      id ∘ id                                                ∎
  }
  where
    open DaggerFunctor
    open NaturalTransformation
