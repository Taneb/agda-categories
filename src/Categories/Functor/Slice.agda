{-# OPTIONS --without-K --safe #-}

open import Categories.Category

module Categories.Functor.Slice {o ℓ e} (C : Category o ℓ e) where

open import Categories.Adjoint
open import Categories.Category.Construction.Pullbacks C
import Categories.Category.Slice as S
open import Categories.Diagram.Pullback C hiding (swap)
open import Categories.Functor hiding (id)
open import Categories.Functor.Properties
open import Categories.Morphism.Reasoning C
open import Categories.NaturalTransformation hiding (id)
open import Categories.Object.Product C

open Category C
open HomReasoning
open Equiv

open S C

module _ {A : Obj} where
  open SliceObj
  open Slice⇒

  Base-F : ∀ {o′ ℓ′ e′} {D : Category o′ ℓ′ e′} (F : Functor C D) → Functor (Slice A) (S.Slice D (Functor.₀ F A))
  Base-F F = record
    { F₀ = λ X → S.sliceobj (F₁ (arr X))
    ; F₁ = λ f → S.slicearr ([ F ]-resp-∘ (△ f))
    ; identity = identity
    ; homomorphism = homomorphism
    ; F-resp-≈ = F-resp-≈
    }
    where open Functor F

  Sigma : Functor (Slice A) C
  Sigma = record
    { F₀ = Y
    ; F₁ = h
    ; identity = refl
    ; homomorphism = refl
    ; F-resp-≈ = λ eq → eq
    }

  module _ (product : ∀ {X} → Product A X) where

    private
      module product {X} = Product (product {X})
      open product

    Delta : Functor C (Slice A)
    Delta = record
      { F₀ = λ _ → sliceobj π₁
      ; F₁ = λ f → slicearr ([ product ⇒ product ]π₁∘× ○ identityˡ)
      ; identity = id×id product
      ; homomorphism = sym [ product ⇒ product ⇒ product ]id×∘id×
      ; F-resp-≈ = λ f≈g → ⟨⟩-cong₂ refl (∘-resp-≈ˡ f≈g)
      }

    Sigma⊣Delta : Sigma ⊣ Delta
    Sigma⊣Delta = record
      { unit = ntHelper record
        { η = λ _ → slicearr project₁
        ; commute = λ {X} {Y} f → begin
          ⟨ arr Y , id ⟩ ∘ h f                            ≈⟨ [ product ]⟨⟩∘ ⟩
          ⟨ arr Y ∘ h f , id ∘ h f ⟩                      ≈⟨ ⟨⟩-cong₂ (△ f) identityˡ ⟩
          ⟨ arr X , h f ⟩                                 ≈˘⟨ ⟨⟩-cong₂ identityˡ identityʳ ⟩
          ⟨ id ∘ arr X , h f ∘ id ⟩                       ≈˘⟨ [ product ⇒ product ]×∘⟨⟩ ⟩
          [ product ⇒ product ] id × h f ∘ ⟨ arr X , id ⟩ ∎
        }
      ; counit = ntHelper record
        { η = λ _ → π₂
        ; commute = λ _ → project₂
        }
      ; zig = project₂
      ; zag = begin
        [ product ⇒ product ]id× π₂ ∘ ⟨ π₁ , id ⟩ ≈⟨ [ product ⇒ product ]id×∘⟨⟩ ⟩
        ⟨ π₁ , π₂ ∘ id ⟩                          ≈⟨ ⟨⟩-cong₂ refl identityʳ ⟩
        ⟨ π₁ , π₂ ⟩                               ≈⟨ η ⟩
        id                                        ∎
      }

  module _ (pullback : ∀ {X Y Z} (h : X ⇒ Z) (i : Y ⇒ Z) → Pullback h i) where

    pullback-functorial : ∀ {B} (f : B ⇒ A) → Functor (Slice A) C
    pullback-functorial f = record
      { F₀ = p.P
      ; F₁ = p⇒
      ; identity = sym (p.unique _ id-comm id-comm)
      ; homomorphism = p.unique-diagram _
        (p.p₁∘universal≈h₁ _ ○ ⟺ identityˡ ○ ⟺ (pullʳ (p.p₁∘universal≈h₁ _)) ○ ⟺ (pullˡ (p.p₁∘universal≈h₁ _)))
        (p.p₂∘universal≈h₂ _ ○ assoc ○ ⟺ (pullʳ (p.p₂∘universal≈h₂ _)) ○ ⟺ (pullˡ (p.p₂∘universal≈h₂ _)))
      ; F-resp-≈ = λ eq → p.unique-diagram _
        (p.p₁∘universal≈h₁ _ ○ ⟺ (p.p₁∘universal≈h₁ _))
        (p.p₂∘universal≈h₂ _ ○ ∘-resp-≈ˡ eq ○ ⟺ (p.p₂∘universal≈h₂ _))
      }
      where
        p : ∀ X → Pullback f (arr X)
        p X = pullback f (arr X)
        module p X = Pullback (p X)

        p⇒ : ∀ {X Y} (g : Slice⇒ X Y) → p.P X ⇒ p.P Y
        p⇒ g = Pullback⇒.pbarr {X = record { pullback = p _ }} {Y = record { pullback = p _ }} record
          { commute₁ = identityʳ
          ; commute₂ = △ g
          }
