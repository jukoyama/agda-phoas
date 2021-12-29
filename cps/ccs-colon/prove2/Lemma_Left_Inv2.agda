{-# OPTIONS --rewriting #-}

module Lemma_Left_Inv2 where

open import DStermK2 hiding (_⇒_cps[_])
open import CPSterm2
open import CPSIsm2
open import DSTrans2

open import Function
open import Relation.Binary.PropositionalEquality
open import Data.Product

open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

dsT∘cpsT𝑘≡id : (τ : typ𝑘) → dsT (cpsT𝑘 τ) ≡ τ
dsT∘cpsT𝑘≡id Nat = refl
dsT∘cpsT𝑘≡id Boolean = refl
dsT∘cpsT𝑘≡id (τ ⇒ τ₁ cps[ τ₂ , τ₃ ]) = begin
    dsT (cpsT𝑘 τ) ⇒ dsT (cpsT𝑘 τ₁) cps[ dsT (cpsT𝑘 τ₂) , dsT (cpsT𝑘 τ₃) ]
  ≡⟨ cong (λ x → x ⇒ dsT (cpsT𝑘 τ₁) cps[ dsT (cpsT𝑘 τ₂) , dsT (cpsT𝑘 τ₃) ])
          (dsT∘cpsT𝑘≡id τ) ⟩
    (τ ⇒ dsT (cpsT𝑘 τ₁) cps[ dsT (cpsT𝑘 τ₂) , dsT (cpsT𝑘 τ₃) ])
  ≡⟨ cong (λ x → τ ⇒ x cps[ dsT (cpsT𝑘 τ₂) , dsT (cpsT𝑘 τ₃) ])
          (dsT∘cpsT𝑘≡id τ₁) ⟩
    (τ ⇒ τ₁ cps[ dsT (cpsT𝑘 τ₂) , dsT (cpsT𝑘 τ₃) ])
  ≡⟨ cong (λ x → τ ⇒ τ₁ cps[ x , dsT (cpsT𝑘 τ₃) ])
          (dsT∘cpsT𝑘≡id τ₂) ⟩
    (τ ⇒ τ₁ cps[ τ₂ , dsT (cpsT𝑘 τ₃) ])
  ≡⟨ cong (λ x → τ ⇒ τ₁ cps[ τ₂ , x ])
          (dsT∘cpsT𝑘≡id τ₃) ⟩
    τ ⇒ τ₁ cps[ τ₂ , τ₃ ]
  ∎
  where open ≡-Reasoning

{-# REWRITE dsT∘cpsT𝑘≡id #-}
Left-InvR : {var : typ𝑘 → Set} → {τ₁ τ₂ τ₃ : typ𝑘} →
            (r : root𝑘[ var ] τ₁ cps[ τ₂ , τ₃ ]) →
            r
            ≡
            dsMain𝑐 (cpsT𝑘 τ₁) (cpsT𝑘 τ₂) (cpsT𝑘 τ₃) (cpsMain𝑘 τ₁ τ₂ τ₃ r)
Left-InvR {var} {τ₁} {τ₂} {τ₃} r =
  begin
    r
  ≡⟨ {!!} ⟩
    dsMain𝑐 (cpsT𝑘 τ₁) (cpsT𝑘 τ₂) (cpsT𝑘 τ₃) (cpsMain𝑘 τ₁ τ₂ τ₃ r)
  ∎
  where open ≡-Reasoning

Left-InvE : {var : typ𝑘 → Set} → {τ₃ τ₅ : typ𝑘} →
            (e : term𝑘[ var ] τ₅ cps[ τ₅ , τ₃ ]) → 
            e
            ≡
            dsE𝑐 (cpsT𝑘 τ₃) (cpsT𝑘 τ₅) (cpsE𝑘 τ₃ τ₅ e)
Left-InvE {var} {τ₃} {τ₅} e =
  begin
    e
  ≡⟨ {!!} ⟩
    dsE𝑐 (cpsT𝑘 τ₃) (cpsT𝑘 τ₅) (cpsE𝑘 τ₃ τ₅ e)
  ∎
  where open ≡-Reasoning

Left-InvV : {var : typ𝑘 → Set} → {τ₁ : typ𝑘} →
            (v : value𝑘[ var ] τ₁ cps[τ,τ]) → 
            v
            ≡
            dsV𝑐 (cpsT𝑘 τ₁) (cpsV𝑘 τ₁ v)
Left-InvV {var} {τ₁} v =
  begin
    v
  ≡⟨ {!!} ⟩
    dsV𝑐 (cpsT𝑘 τ₁) (cpsV𝑘 τ₁ v)
  ∎
  where open ≡-Reasoning          

Left-InvC : {var : typ𝑘 → Set} → {τ₁ τ₂ τ₃ τ₅ : typ𝑘} →
            (k : pcontext𝑘[ var , τ₁ cps[ τ₂ , τ₃ ]] τ₅
                         cps[ τ₅ , τ₃ ]) → 
            k
            ≡
            dsC𝑐 (cpsT𝑘 τ₁) (cpsT𝑘 τ₂) (cpsT𝑘 τ₃) (cpsT𝑘 τ₅)
                 (cpsC𝑘 τ₁ τ₂ τ₃ τ₅ k)
Left-InvC {var} {τ₁} {τ₂} {τ₃} {τ₅} k =
  begin
    k
  ≡⟨ {!!} ⟩
    {!!}
  ∎
  where open ≡-Reasoning          
