{-# OPTIONS --without-K --safe #-}
module Categories.Functor.Equivalence where

-- A 'strict' equality of Functor. Need object equality so that hom-equality is well-typed
-- Go full-strict, so that ≡ is used for Hom too, even though ≈ would be well-typed.
open import Level
open import Data.Product using (Σ; proj₁; proj₂; map) renaming (_,_ to _,,_)
open import Relation.Binary.PropositionalEquality
open import Relation.Binary using (IsEquivalence)
open import Function using (_$_) renaming (_∘_ to _⊚_)

open import Categories.Category using (Category; _[_,_])
open import Categories.Functor using (Functor; id; _∘F_)
open import Categories.Utils.EqReasoning

private
  variable
    o ℓ e o′ ℓ′ e′ o″ ℓ″ e″ : Level

-- "extensional" equality of Functors. A Heterogeneous equality, specialized for this case.
infix  4 _≡F_

_≡F_ : {C : Category o ℓ e} {D : Category o′ ℓ′ e′} (F G : Functor C D) → Set (ℓ ⊔ o ⊔ o′ ⊔ ℓ′)
_≡F_ {C = C} {D = D} F G = {A B : Category.Obj C} → (f : C [ A , B ]) →
  Σ ((X : Category.Obj C) → Functor.F₀ F X ≡ Functor.F₀ G X)
    (λ eq → subst₂ _⇒_ (eq A) (eq B) (Functor.F₁ F f) ≡ Functor.F₁ G f)
  where open Category D
    -- Note that
    -- (λ eq → subst₂ _⇒_ (eq {A}) (eq {B}) (Functor.F₁ F f) ≈ Functor.F₁ G f)
    -- would be well-typed too.

≡F-equiv : {C : Category o ℓ e} {D : Category o′ ℓ′ e′} → IsEquivalence (_≡F_ {C = C} {D})
≡F-equiv {C = C} {D} = record
  { refl = λ f → (λ _ → refl) ,, refl
  ; sym = λ {i} {j} i≡j f → map (λ eq → sym ⊚ eq ) (λ {eq} eqs → sym2 i j i≡j eq eqs) (i≡j f)
  ; trans = λ {i} {j} {k} i≡j j≡k {A} {B} f →
              (λ X → trans (proj₁ (i≡j f) X) (proj₁ (j≡k f) X)) ,,
              trans2 i j k i≡j j≡k
  }
  where
  open Category D
  open ≡-Reasoning
  sym2 : (i j : Functor C D) (i≡j : i ≡F j) {A B : Category.Obj C} {f : Category._⇒_ C A B}
         (eq :  (x : Category.Obj C) → Functor.F₀ i x ≡ Functor.F₀ j x) →
         subst₂ (_⇒_) (eq A) (eq B) (Functor.F₁ i f) ≡ Functor.F₁ j f →
         subst₂ (_⇒_) (sym (eq A)) (sym (eq B)) (Functor.F₁ j f) ≡ Functor.F₁ i f
  sym2 i j i≡j {A} {B} {f} eq eqs = begin
    subst₂ (_⇒_) (sym (eq A)) (sym (eq B)) (Functor.F₁ j f) ≡⟨ cong (subst₂ (_⇒_) (sym $ eq A) (sym $ eq B)) (sym eqs) ⟩
    subst₂ _⇒_ (sym (eq A)) (sym (eq B))
      (subst₂ _⇒_ (eq A) (eq B) (Functor.F₁ i f))           ≡⟨ subst₂-sym-subst₂ _⇒_ (eq A) (eq B) ⟩
    Functor.F₁ i f ∎
  trans2 : (i j k : Functor C D) (i≡j : i ≡F j) (j≡k : j ≡F k) {A B : Category.Obj C} {f : Category._⇒_ C A B} →
           subst₂ _⇒_ (trans (proj₁ (i≡j f) A) (proj₁ (j≡k f) A)) (trans (proj₁ (i≡j f) B) (proj₁ (j≡k f) B)) (Functor.F₁ i f)
           ≡ Functor.F₁ k f
  trans2 i j k i≡j j≡k {A} {B} {f} =
    let i≡jA = proj₁ (i≡j f) A in
    let j≡kA = proj₁ (j≡k f) A in
    let i≡jB = proj₁ (i≡j f) B in
    let j≡kB = proj₁ (j≡k f) B in
    let eqA = trans i≡jA j≡kA in
    let eqB = trans i≡jB j≡kB in begin
    subst₂ _⇒_ eqA eqB (Functor.F₁ i f)           ≡˘⟨ subst₂-subst₂ _⇒_ i≡jA j≡kA _ _ ⟩
    subst₂ _⇒_ j≡kA j≡kB (subst₂ _⇒_ i≡jA i≡jB _) ≡⟨ cong (subst₂ _⇒_ _ _) (proj₂ (i≡j f)) ⟩
    subst₂ _⇒_ j≡kA j≡kB (Functor.F₁ j f)         ≡⟨ proj₂ (j≡k f) ⟩
    Functor.F₁ k f ∎

-- Since the above isn't just ≡, it is convenient to also prove here that ≡F is preserved by ∘F
-- Note that this proof below is "the same" as horizontal composition of NaturalIsomorphism _ⓘₕ_
∘F-perserves-≡F : {A : Category o ℓ e} {B : Category o′ ℓ′ e′} {C : Category o″ ℓ″ e″} {h i : Functor B C} {f g : Functor A B} →
      h ≡F i → f ≡F g → h ∘F f ≡F i ∘F g
∘F-perserves-≡F {A = A} {B} {C} {h} {i} {f} {g} h≡i f≡g {a₁} {a₂} a₁⇒a₂ = obj-≡ ,, hom-≡
  where
  open Functor
  open Category C
  module B = Category B
  open ≡-Reasoning
  obj-≡ : (X : Category.Obj A) → F₀ h (F₀ f X) ≡ F₀ i (F₀ g X)
  obj-≡ X = trans (cong (F₀ h) (proj₁ (f≡g a₁⇒a₂) X)) (proj₁ (h≡i $ F₁ g a₁⇒a₂) _)
  hom-≡ : subst₂ _⇒_ (obj-≡ a₁) (obj-≡ a₂) (F₁ h (F₁ f a₁⇒a₂)) ≡ F₁ i (F₁ g a₁⇒a₂)
  hom-≡ =
    let Ff = F₁ f a₁⇒a₂ in
    let Fg = F₁ g a₁⇒a₂ in
    let eq₁ X = proj₁ (h≡i Fg) X in
    let eq₂ X = proj₁ (f≡g a₁⇒a₂) X in
    let eq₃ X = cong (F₀ h) (eq₂ X) in
    let s = subst₂ _⇒_ (eq₁ _) (eq₁ _) in
    begin
    subst₂ _⇒_ (obj-≡ a₁) (obj-≡ a₂) (F₁ h Ff)   ≡˘⟨ subst₂-subst₂ _⇒_ (eq₃ _) (eq₁ _) (eq₃ _) (eq₁ _) ⟩
    s (subst₂ _⇒_ (eq₃ _) (eq₃ _) (F₁ h Ff))     ≡⟨ cong s (subst₂-app _⇒_ Ff (λ _ _ x → F₁ h x) (eq₂ _) (eq₂ _)) ⟩
    s (F₁ h (subst₂ B._⇒_ (eq₂ _) (eq₂ _) Ff))   ≡⟨ cong s $ cong (F₁ h) $ proj₂ (f≡g a₁⇒a₂) ⟩
    subst₂ _⇒_ (eq₁ _) (eq₁ _) (F₁ h Fg)         ≡⟨ proj₂ (h≡i Fg) ⟩
    F₁ i (F₁ g a₁⇒a₂) ∎