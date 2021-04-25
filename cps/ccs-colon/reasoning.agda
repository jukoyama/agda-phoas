module reasoning where

open import DSterm
open import CPSterm
open import Relation.Binary.PropositionalEquality

infix  3 _∎
infixr 2 _⟶⟨_⟩_ _⟵⟨_⟩_ _⟷⟨_⟩_ _≡⟨_⟩_
infix  1 begin_

begin_ : {var : cpstyp → Set} {τ₁ : cpstyp} →
         {e₁ e₂ : cpsterm𝑐[ var ] τ₁} →
         cpsReduce e₁ e₂ → cpsReduce e₁ e₂
begin_ red = red

_⟶⟨_⟩_ : {var : cpstyp → Set} {τ₁ : cpstyp} →
          (e₁ {e₂ e₃} : cpsterm𝑐[ var ] τ₁) →
          cpsReduce e₁ e₂ → cpsReduce e₂ e₃ → cpsReduce e₁ e₃
_⟶⟨_⟩_ e₁ {e₂} {e₃} e₁-eq-e₂ e₂-eq-e₃ = RTrans𝑐 e₁ e₂ e₃ e₁-eq-e₂ e₂-eq-e₃

_⟵⟨_⟩_ : {var : cpstyp → Set} {τ₁ : cpstyp} →
          (e₁ {e₂ e₃} : cpsterm𝑐[ var ] τ₁) →
          cpsReduce e₂ e₁ → cpsReduce e₂ e₃ → cpsReduce e₁ e₃
_⟵⟨_⟩_ e₁ {e₂} {e₃} e₂-eq-e₁ e₂-eq-e₃ = RTrans𝑐′ e₁ e₂ e₃ e₂-eq-e₁ e₂-eq-e₃

_⟷⟨_⟩_ : {var : cpstyp → Set} {τ₁ : cpstyp} →
          (e₁ {e₂ e₃} : cpsterm𝑐[ var ] τ₁) →
          cpsReduce e₁ e₂ → cpsReduce e₂ e₃ → cpsReduce e₁ e₃
_⟷⟨_⟩_ e₁ {e₂} {e₃} e₁-eq-e₂ e₂-eq-e₃ = RTrans𝑐 e₁ e₂ e₃ e₁-eq-e₂ e₂-eq-e₃

_≡⟨_⟩_ : {var : cpstyp → Set} {τ₁ : cpstyp} →
         (e₁ {e₂ e₃} : cpsterm𝑐[ var ] τ₁) → e₁ ≡ e₂ → cpsReduce e₂ e₃ →
           cpsReduce e₁ e₃
_≡⟨_⟩_ e₁ {e₂} {e₃} refl e₂-eq-e₃ = e₂-eq-e₃

_∎ : {var : cpstyp → Set} {τ₁ : cpstyp} →
     (e : cpsterm𝑐[ var ] τ₁) → cpsReduce e e
_∎ e = RId𝑐
