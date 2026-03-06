{-# OPTIONS --safe --without-K #-}

module Categories.Category.Construction.DaggerFunctors where

open import Categories.Category.Core using (Category)
open import Categories.Category.Construction.Functors using (Functors)
open import Categories.Category.SubCategory using (FullSubCategory)
open import Categories.Category.Dagger using (DaggerCategory)
open import Categories.Category.Product using (_⁂_; assocˡ)
open import Categories.Functor using (_∘F_) renaming (id to idF)
open import Categories.Functor.Bifunctor using (Bifunctor)
open import Categories.Functor.Dagger using (DaggerFunctor; _∘F†_)
import Categories.Morphism.Reasoning as MR
open import Categories.NaturalTransformation using (NaturalTransformation; _∘ₕ_; ntHelper)
open import Categories.NaturalTransformation.NaturalIsomorphism using (NaturalIsomorphism; niHelper)

open import Data.Product.Base using (_,_; proj₁; uncurry)
open import Level using (Level; _⊔_)

private
  variable
    o ℓ e o′ ℓ′ e′ : Level
    A B C D : DaggerCategory o ℓ e

DaggerFunctors : DaggerCategory o ℓ e → DaggerCategory o′ ℓ′ e′ → Category (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′ ⊔ e′) (o ⊔ ℓ ⊔ ℓ′ ⊔ e′) (o ⊔ e′)
DaggerFunctors C D = FullSubCategory (Functors (DaggerCategory.C C) (DaggerCategory.C D)) {I = DaggerFunctor C D} DaggerFunctor.functor

product : Bifunctor (DaggerFunctors B C) (DaggerFunctors A B) (DaggerFunctors A C)
product {B = B} {C = C} = record
  { F₀ = uncurry _∘F†_
  ; F₁ = uncurry _∘ₕ_
  ; identity = λ {F} → identityʳ ○ identity (proj₁ F)
  ; homomorphism = λ {_} {(G₁ , _)} {(H₁ , _)} {(f₁ , f₂)} {(g₁ , g₂)} → begin
      F₁ H₁ (η g₂ _ B.∘ η f₂ _) ∘ η g₁ _ ∘ η f₁ _  ≈⟨ ∘-resp-≈ˡ (homomorphism H₁) ⟩
      (F₁ H₁ (η g₂ _) ∘ F₁ H₁ _) ∘ η g₁ _ ∘ η f₁ _ ≈⟨ extend² (sym-commute g₁ (η f₂ _)) ⟩
      (F₁ H₁ (η g₂ _) ∘ η g₁ _) ∘ F₁ G₁ _ ∘ η f₁ _ ∎
  ; F-resp-≈ = λ {_} {(G₁ , _)} (≈₁ , ≈₂) → ∘-resp-≈ (F-resp-≈ G₁ ≈₂) ≈₁
  }
  where
    open DaggerCategory C renaming (C to U)
    open MR U
    open HomReasoning
    open DaggerFunctor
    module B = DaggerCategory B
    open NaturalTransformation

product-assoc : NaturalIsomorphism
  (product ∘F (product ⁂ idF))
  (product ∘F (idF ⁂ product) ∘F (assocˡ (DaggerFunctors C D) (DaggerFunctors B C) (DaggerFunctors A B)))
product-assoc {C = C} {D = D} = niHelper record
  { η = λ _ → ntHelper record
    { η = λ _ → id
    ; commute = λ _ → id-comm-sym
    }
  ; η⁻¹ = λ _ → ntHelper record
    { η = λ _ → id
    ; commute = λ _ → id-comm-sym
    }
  ; commute = λ {_} {((F , G) , _)} ((α , β) , γ) → begin
    id ∘ (F₁ F (F₁ G (η γ _)) ∘ (F₁ F (η β _) ∘ η α _)) ≈⟨ refl⟩∘⟨ pushˡ (homomorphism F) ⟨
    id ∘ (F₁ F (F₁ G (η γ _) C.∘ η β _) ∘ η α _)        ≈⟨ id-comm-sym ⟩
    (F₁ F (F₁ G (η γ _) C.∘ η β _) ∘ η α _) ∘ id        ∎
  ; iso = λ ((F , G) , H) → record
    { isoˡ = identity²
    ; isoʳ = identity²
    }
  }
  where
    open DaggerCategory D renaming (C to U)
    open MR U
    open HomReasoning
    module C = DaggerCategory C
    open DaggerFunctor
    open NaturalTransformation
