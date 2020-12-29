module reasoning where

open import DSterm
open import CPSterm
open import Relation.Binary.PropositionalEquality

infix  3 _∎
infixr 2 _⟶⟨_⟩_ _⟵⟨_⟩_ _⟷⟨_⟩_ _≡⟨_⟩_
infix  1 begin_

begin_ : {var : cpstyp → Set} {τ₁ : cpstyp} →
         {e₁ e₂ : cpsterm[ var ] τ₁} →
         cpsequal e₁ e₂ → cpsequal e₁ e₂
begin_ red = red

_⟶⟨_⟩_ : {var : cpstyp → Set} {τ₁ : cpstyp} →
          (e₁ {e₂ e₃} : cpsterm[ var ] τ₁) →
          cpsequal e₁ e₂ → cpsequal e₂ e₃ → cpsequal e₁ e₃
_⟶⟨_⟩_ e₁ {e₂} {e₃} e₁-eq-e₂ e₂-eq-e₃ = eqTrans e₁ e₂ e₃ e₁-eq-e₂ e₂-eq-e₃

_⟵⟨_⟩_ : {var : cpstyp → Set} {τ₁ : cpstyp} →
          (e₁ {e₂ e₃} : cpsterm[ var ] τ₁) →
          cpsequal e₂ e₁ → cpsequal e₂ e₃ → cpsequal e₁ e₃
_⟵⟨_⟩_ e₁ {e₂} {e₃} e₂-eq-e₁ e₂-eq-e₃ = eqTrans′ e₁ e₂ e₃ e₂-eq-e₁ e₂-eq-e₃

_⟷⟨_⟩_ : {var : cpstyp → Set} {τ₁ : cpstyp} →
          (e₁ {e₂ e₃} : cpsterm[ var ] τ₁) →
          cpsequal e₁ e₂ → cpsequal e₂ e₃ → cpsequal e₁ e₃
_⟷⟨_⟩_ e₁ {e₂} {e₃} e₁-eq-e₂ e₂-eq-e₃ = eqTrans e₁ e₂ e₃ e₁-eq-e₂ e₂-eq-e₃

_≡⟨_⟩_ : {var : cpstyp → Set} {τ₁ : cpstyp} →
         (e₁ {e₂ e₃} : cpsterm[ var ] τ₁) → e₁ ≡ e₂ → cpsequal e₂ e₃ →
           cpsequal e₁ e₃
_≡⟨_⟩_ e₁ {e₂} {e₃} refl e₂-eq-e₃ = e₂-eq-e₃

_≡₁⟨_⟩_ : {var : cpstyp → Set} {τ₁ : cpstyp} →
         (e₁ {e₂ e₃} : cpsterm[ var ] τ₁) →
         cpsRefl e₁ e₂ → cpsequal e₂ e₃ →
         cpsequal e₁ e₃
_≡₁⟨_⟩_ e₁ {e₂} {e₃} e₁-refl-e₂ e₂-eq-e₃ = eqTrans e₁ e₂ e₃ (eqRefl e₁ e₂ e₁-refl-e₂) e₂-eq-e₃

_∎ : {var : cpstyp → Set} {τ₁ : cpstyp} →
     (e : cpsterm[ var ] τ₁) → cpsequal e e
_∎ e = eqId

infix  3 _∎₂
infixr 2 _⟶₂⟨_⟩_ _≡₂⟨_⟩_
infix  1 begin₂_

begin₂_ : {var : cpstyp → Set} {τ₁ : cpstyp} →
         {e₁ e₂ : cpsterm[ var ] τ₁} →
         cpsRefl e₁ e₂ → cpsRefl e₁ e₂
begin₂_ red = red

_⟶₂⟨_⟩_ : {var : cpstyp → Set} {τ₁ : cpstyp} →
          (e₁ {e₂ e₃} : cpsterm[ var ] τ₁) →
          cpsRefl e₁ e₂ → cpsRefl e₂ e₃ → cpsRefl e₁ e₃
_⟶₂⟨_⟩_ e₁ {e₂} {e₃} e₁-refl-e₂ e₂-refl-e₃ = Trans* e₁ e₂ e₃ e₁-refl-e₂ e₂-refl-e₃

_≡₂⟨_⟩_ : {var : cpstyp → Set} {τ₁ : cpstyp} →
         (e₁ {e₂ e₃} : cpsterm[ var ] τ₁) → e₁ ≡ e₂ → cpsRefl e₂ e₃ →
           cpsRefl e₁ e₃
_≡₂⟨_⟩_ e₁ {e₂} {e₃} refl e₂-refl-e₃ = e₂-refl-e₃

_∎₂ : {var : cpstyp → Set} {τ₁ : cpstyp} →
     (e : cpsterm[ var ] τ₁) → cpsRefl e e
_∎₂ e = eqId
