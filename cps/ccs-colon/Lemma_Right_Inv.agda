module Lemma_Right_Inv where

open import DStermK
open import CPSterm
open import CPSIsm
open import DSTrans

open import Relation.Binary.PropositionalEquality
open import Data.Product

cpstyp≡ : ∀ (τ : cpstyp) → cpsT𝑘 (dsT τ) ≡ τ
cpstyp≡ Nat     = refl
cpstyp≡ Boolean = refl
cpstyp≡ (τ₁ ⇒[ τ₂ ⇒ τ₃ ]⇒ τ₄)
  rewrite cpstyp≡ τ₁ | cpstyp≡ τ₂ | cpstyp≡ τ₃ | cpstyp≡ τ₄ = refl

Right_Inv : {var : cpstyp → Set} → {τ₁ τ₂ τ₃ : cpstyp} →
            {e : (var (τ₁ ⇒[ (τ₂ ⇒ τ₂) ]⇒ τ₂) → cpsterm𝑐[ var ] (τ₂ ⇒ τ₂) τ₃)} →
            cpsMain𝑘 (dsT τ₁) (dsT τ₂) (dsT τ₃) (dsMain𝑐 τ₁ τ₂ τ₃ e)
            ≡
            {!e!}
Right_Inv = {!!}
