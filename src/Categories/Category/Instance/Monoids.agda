{-# OPTIONS --without-K --safe #-}
module Categories.Category.Instance.Monoids where

-- This module defines the category of monoids and monoid morphisms, using the
-- stdlib definition of those.

-- It is equivalent to Categories.Category.Construction.Monoids (Categories.Category.Instance.Setoids c ℓ)

open import Categories.Category.Core

open import Algebra
open import Algebra.Morphism
open import Data.Product
open import Function
open import Level

open Monoid
open IsMonoidMorphism

Monoids : (c ℓ : Level) → Category (suc (c ⊔ ℓ)) (c ⊔ ℓ) (c ⊔ ℓ)
Monoids c ℓ = record
  { Obj = Monoid c ℓ
  ; _⇒_ = λ M N → Σ (Carrier M → Carrier N) (IsMonoidMorphism M N)
  ; _≈_ = λ {M} {N} f g → ∀ {x y} → _≈_ M x y → _≈_ N (proj₁ f x) (proj₁ g y)
  ; id = λ {M} → (λ m → m) , record
    { sm-homo = record
      { ⟦⟧-cong = λ p → p
      ; ∙-homo = λ x y → refl M
      }
    ; ε-homo = refl M
    }
  ; _∘_ = λ {M} {N} {O} f g → proj₁ f ∘ proj₁ g , record
    { sm-homo = record
      { ⟦⟧-cong = λ p → ⟦⟧-cong (proj₂ f) (⟦⟧-cong (proj₂ g) p)
      ; ∙-homo = λ x y → trans O (⟦⟧-cong (proj₂ f) (∙-homo (proj₂ g) x y)) (∙-homo (proj₂ f) _ _)
      }
    ; ε-homo = trans O (⟦⟧-cong (proj₂ f) (ε-homo (proj₂ g))) (ε-homo (proj₂ f))
    }
  ; assoc = λ {M} {N} {O} {P} {f} {g} {h} p → ⟦⟧-cong (proj₂ h) (⟦⟧-cong (proj₂ g) (⟦⟧-cong (proj₂ f) p))
  ; sym-assoc = λ {M} {N} {O} {P} {f} {g} {h} p → ⟦⟧-cong (proj₂ h) (⟦⟧-cong (proj₂ g) (⟦⟧-cong (proj₂ f) p))
  ; identityˡ = λ {M} {N} {f} p → ⟦⟧-cong (proj₂ f) p
  ; identityʳ = λ {M} {N} {f} p → ⟦⟧-cong (proj₂ f) p
  ; identity² = λ p → p
  ; equiv = λ {M} {N} → record
    { refl = λ {f} p → ⟦⟧-cong (proj₂ f) p
    ; sym = λ {f} {g} f≈g x≈y → sym N (f≈g (sym M x≈y))
    ; trans = λ {f} {g} {h} f≈g g≈h x≈y → trans N (f≈g x≈y) (g≈h (refl M))
    }
  ; ∘-resp-≈ = λ {M} {N} {O} {f} {f′} {g} {g′} f≈f′ g≈g′ x≈y → trans O (⟦⟧-cong (proj₂ f) (g≈g′ x≈y)) (f≈f′ (refl N))
  }
