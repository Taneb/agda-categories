{-# OPTIONS --safe --without-K #-}

module Categories.Category.Instance.Properties.Cats.Complete where

open import Categories.Category
open import Categories.Category.Instance.Cats
import Categories.Diagram.Equalizer as Equalizer
open import Categories.Functor
import Categories.Morphism as Morphism
import Categories.Morphism.Reasoning as MorphismReasoning
open import Categories.NaturalTransformation.NaturalIsomorphism

open import Level


-- Cats has all equalizers

module _ {o ℓ e : Level} {C D : Category (o ⊔ ℓ ⊔ e) (ℓ ⊔ e) e} (F G : Functor C D) where

  module C = Category C
  module F = Functor F
  module G = Functor G

  open Category D
  open HomReasoning
  open Morphism D
  open MorphismReasoning D

  open Equalizer (Cats (o ⊔ ℓ ⊔ e) (ℓ ⊔ e) e)

  record CEO : Set (o ⊔ ℓ ⊔ e) where
    field
      obj : C.Obj
      iso : F.₀ obj ≅ G.₀ obj
    module iso = _≅_ iso

  record CE⇒ (X Y : CEO) : Set (ℓ ⊔ e) where
    private
      module X = CEO X
      module Y = CEO Y
    field
      arr : C [ X.obj , Y.obj ]
      commute : Y.iso.from ∘ F.₁ arr ≈ G.₁ arr ∘ X.iso.from
      
  CE : Category (o ⊔ ℓ ⊔ e) (ℓ ⊔ e) e
  CE = record
    { Obj = CEO
    ; _⇒_ = CE⇒
    ; _≈_ = λ f g → C [ CE⇒.arr f ≈ CE⇒.arr g ]
    ; id = λ {A} → let module A = CEO A in record
      { arr = C.id
      ; commute = begin
        A.iso.from ∘ F.₁ C.id ≈⟨ elimʳ F.identity ⟩
        A.iso.from            ≈⟨ introˡ G.identity ⟩
        G.₁ C.id ∘ A.iso.from ∎
      }
    ; _∘_ = λ {X} {Y} {Z} f g →
      let
        module X = CEO X
        module Y = CEO Y
        module Z = CEO Z
        module f = CE⇒ f
        module g = CE⇒ g
      in record
        { arr = C [ f.arr ∘ g.arr ]
        ; commute = begin
          Z.iso.from ∘ F.₁ (C [ f.arr ∘ g.arr ]) ≈⟨ refl⟩∘⟨ F.homomorphism ⟩
          Z.iso.from ∘ (F.₁ f.arr ∘ F.₁ g.arr)   ≈⟨ sym-assoc ⟩
          (Z.iso.from ∘ F.₁ f.arr) ∘ F.₁ g.arr   ≈⟨ f.commute ⟩∘⟨refl ⟩
          (G.₁ f.arr ∘ Y.iso.from) ∘ F.₁ g.arr   ≈⟨ assoc ⟩
          G.₁ f.arr ∘ (Y.iso.from ∘ F.₁ g.arr)   ≈⟨ refl⟩∘⟨ g.commute ⟩
          G.₁ f.arr ∘ (G.₁ g.arr ∘ X.iso.from)   ≈⟨ sym-assoc ⟩
          (G.₁ f.arr ∘ G.₁ g.arr) ∘ X.iso.from   ≈˘⟨ G.homomorphism ⟩∘⟨refl ⟩
          G.₁ (C [ f.arr ∘ g.arr ]) ∘ X.iso.from ∎
        }
    ; assoc = C.assoc
    ; sym-assoc = C.sym-assoc
    ; identityˡ = C.identityˡ
    ; identityʳ = C.identityʳ
    ; identity² = C.identity²
    ; equiv = record
      { refl = C.Equiv.refl
      ; sym = C.Equiv.sym
      ; trans = C.Equiv.trans
      }
    ; ∘-resp-≈ = C.∘-resp-≈
    }

  CE⇒C : Functor CE C
  CE⇒C = record
    { F₀ = CEO.obj
    ; F₁ = CE⇒.arr
    ; identity = C.Equiv.refl
    ; homomorphism = C.Equiv.refl
    ; F-resp-≈ = λ f≈g → f≈g
    }

  CE⇒C-isEqualizer : IsEqualizer CE⇒C F G
  CE⇒C-isEqualizer = record
    { equality = niHelper record
      { η = CEO.iso.from
      ; η⁻¹ = CEO.iso.to
      ; commute = CE⇒.commute
      ; iso = CEO.iso.iso
      }
    ; equalize = λ {X} {h} F∘h≃G∘h → record
      { F₀ = λ x → record
        { obj = Functor.₀ h x
        ; iso = record
          { iso = NaturalIsomorphism.iso F∘h≃G∘h x
          }
        }
      ; F₁ = λ f → record
        { arr = Functor.₁ h f
        ; commute = NaturalIsomorphism.⇒.commute F∘h≃G∘h f
        }
      ; identity = Functor.identity h
      ; homomorphism = Functor.homomorphism h
      ; F-resp-≈ = Functor.F-resp-≈ h
      }
    ; universal = λ {X} {h} {F∘h≃G∘h} → niHelper record
      { η = λ x → C.id
      ; η⁻¹ = λ x → C.id
      ; commute = λ f → MorphismReasoning.id-comm-sym C
      ; iso = λ x → record
        { isoˡ = C.identity²
        ; isoʳ = C.identity²
        }
      }
    ; unique = λ {X} {h} {i} {F∘h≃G∘h} h≃CE⇒C∘i → niHelper record
      { η = λ x → record
        { arr = NaturalIsomorphism.⇐.η h≃CE⇒C∘i x
        ; commute = begin
          NaturalIsomorphism.⇒.η F∘h≃G∘h x ∘ F.₁ (NaturalIsomorphism.⇐.η h≃CE⇒C∘i x) ≈⟨ {!!} ⟩
          G.₁ (NaturalIsomorphism.⇐.η h≃CE⇒C∘i x) ∘ CEO.iso.from (Functor.₀ i x)     ∎
        }
      ; η⁻¹ = {!!}
      ; commute = λ f → NaturalIsomorphism.⇐.commute h≃CE⇒C∘i f
      ; iso = λ x → record
        { isoˡ = NaturalIsomorphism.iso.isoʳ h≃CE⇒C∘i x
        ; isoʳ = NaturalIsomorphism.iso.isoˡ h≃CE⇒C∘i x
        }
      }
    }

  equalizer : Equalizer F G
  equalizer = record
    { arr = CE⇒C
    ; isEqualizer = CE⇒C-isEqualizer
    }
