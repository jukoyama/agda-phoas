{-# OPTIONS --rewriting #-}

module Lemma_Left_Inv where

open import DStermK
open import CPSterm
open import CPSIsm
open import DSTrans

open import Function
open import Relation.Binary.PropositionalEquality hiding (Extensionality)
open import Data.Product

open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

open import Level using (Level)
open import Axiom.Extensionality.Propositional

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

dsT𝑐∘cpsT𝑘𝑐≡id : (τ : typ𝑘𝑐) → dsT𝑐 (cpsT𝑘𝑐 τ) ≡ τ
dsT𝑐∘cpsT𝑘𝑐≡id (τ₂ ▷ τ₁) =
  cong₂ _▷_ (dsT∘cpsT𝑘≡id τ₂) (dsT∘cpsT𝑘≡id τ₁)

postulate
  extensionality : {a b : Level} → Extensionality a b

{-# REWRITE dsT∘cpsT𝑘≡id dsT𝑐∘cpsT𝑘𝑐≡id #-}
mutual
  Left-InvV : {var : typ𝑘 → Set} {cvar : typ𝑘𝑐 → Set} → {τ₁ : typ𝑘} →
              (v : value𝑘[ var , cvar ] τ₁ cps[τ,τ]) →
              v ≡ dsV𝑐 {τ₁ = cpsT𝑘 τ₁} (cpsV𝑘 v)
  Left-InvV (Num n) = refl
  Left-InvV (Var x) = refl
  Left-InvV (Fun e) =
    cong Fun (extensionality (λ x → extensionality (λ k → Left-InvE (e x k))))
  Left-InvV Shift = refl

  Left-InvE : {var : typ𝑘 → Set} {cvar : typ𝑘𝑐 → Set} → {τ : typ𝑘} →
              (e : term𝑘[ var , cvar ] τ) →
              e ≡ dsE𝑐 {τ = cpsT𝑘 τ} (cpsE𝑘 e)
  Left-InvE (Ret k v) = cong₂ Ret (Left-InvC k) (Left-InvV v)
  Left-InvE (App v w k) = begin
      App v w k
    ≡⟨ cong (λ x → x k) (cong₂ App (Left-InvV v) (Left-InvV w)) ⟩
      App (dsV𝑐 (cpsV𝑘 v)) (dsV𝑐 {τ₁ = cpsT𝑘 _} (cpsV𝑘 w)) k
    ≡⟨ cong (App _ _) (Left-InvC k) ⟩
      App (dsV𝑐 (cpsV𝑘 v)) (dsV𝑐 {τ₁ = cpsT𝑘 _} (cpsV𝑘 w))
          (dsC𝑐 {τ₁ = cpsT𝑘 _} {τ₂ = cpsT𝑘 _} (cpsC𝑘 k))
    ∎
    where open ≡-Reasoning
  Left-InvE (RetE k e) = cong₂ RetE (Left-InvC k) (Left-InvE e)

  Left-InvC : {var : typ𝑘 → Set} {cvar : typ𝑘𝑐 → Set} → {τ₁ τ₂ : typ𝑘} →
              (k : pcontext𝑘[ var , cvar ] (τ₁ ▷ τ₂)) →
              k ≡ dsC𝑐 {τ₁ = cpsT𝑘 τ₁} {τ₂ = cpsT𝑘 τ₂} (cpsC𝑘 k)
  Left-InvC (KHole k) = refl
  Left-InvC Hole = refl
  Left-InvC (KLet e) = cong KLet (extensionality (λ x → Left-InvE (e x)))
