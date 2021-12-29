{-# OPTIONS --rewriting #-}

module Lemma_Right_Inv2 where

open import DStermK2 hiding (_⇒_cps[_])
open import CPSterm2
open import CPSIsm2
open import DSTrans2

open import Function
open import Relation.Binary.PropositionalEquality
open import Data.Product

open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

cpsT𝑘∘dsT≡id : (τ : cpstyp) → cpsT𝑘 (dsT τ) ≡ τ
cpsT𝑘∘dsT≡id Nat     = refl
cpsT𝑘∘dsT≡id Boolean = refl
cpsT𝑘∘dsT≡id (τ ⇒[ τ₁ ⇒ τ₂ ]⇒ τ₃) = {!!}

{-# REWRITE cpsT𝑘∘dsT≡id #-}
Right-InvR : {var : cpstyp → Set} → {τ₁ τ₂ τ₃ : cpstyp} →
             (r : (var (τ₁ ⇒[ (τ₂ ⇒ τ₂) ]⇒ τ₂) → cpsterm𝑐[ var ] (τ₂ ⇒ τ₂) τ₃)) →
             cpsMain𝑘 (dsT τ₁) (dsT τ₂) (dsT τ₃) (dsMain𝑐 τ₁ τ₂ τ₃ r)
              ≡
             r
Right-InvR {var} {τ₁} {τ₂} {τ₃} r =
  begin
    cpsMain𝑘 (dsT τ₁) (dsT τ₂) (dsT τ₃) (dsMain𝑐 τ₁ τ₂ τ₃ r)
  ≡⟨ {!!} ⟩
    r
  ∎
  where open ≡-Reasoning          

Right-InvE : {var : typ𝑘 → Set} → {τ₃ τ₅ : cpstyp} →
             (e : cpsterm𝑐[ var ∘ dsT ] (τ₅ ⇒ τ₅) τ₃) →
             cpsE𝑘 (dsT τ₃) (dsT τ₅) (dsE𝑐 τ₃ τ₅ e)
             ≡
             e
Right-InvE {var} {τ₃} {τ₅} e =
  begin
    {!!}
  ≡⟨ {!!} ⟩
    e
  ∎
  where open ≡-Reasoning          

Right-InvV : {var : typ𝑘 → Set} → {τ₁ : cpstyp} →
             (v : cpsvalue𝑐[ var ∘ dsT ] τ₁) →
             cpsV𝑘 (dsT τ₁) (dsV𝑐 τ₁ v)
             ≡
             v
Right-InvV {var} {τ₁} v =
  begin
    {!!}
  ≡⟨ {!!} ⟩
    v
  ∎
  where open ≡-Reasoning          

Right-InvC : {var : typ𝑘 → Set} → {τ₁ τ₂ τ₃ τ₅ : cpstyp} →
             (k : cpscont𝑐[ var ∘ dsT ] (τ₅ ⇒ τ₅) τ₃ (τ₁ ⇒ τ₂)) →
             cpsC𝑘 (dsT τ₁) (dsT τ₂) (dsT τ₃) (dsT τ₅)
                   (dsC𝑐 τ₁ τ₂ τ₃ τ₅ k)
             ≡
             k
Right-InvC {var} {τ₁} {τ₂} {τ₃} {τ₅} k =
  begin
    {!!}
  ≡⟨ {!!} ⟩
    k
  ∎
  where open ≡-Reasoning          

