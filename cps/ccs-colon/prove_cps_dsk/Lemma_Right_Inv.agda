{-# OPTIONS --rewriting #-}

module Lemma_Right_Inv where

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

cpsT𝑘∘dsT≡id : (τ : cpstyp) → cpsT𝑘 (dsT τ) ≡ τ
cpsT𝑘∘dsT≡id Nat     = refl
cpsT𝑘∘dsT≡id Boolean = refl
cpsT𝑘∘dsT≡id (τ ⇒[ τ₁ ⇒ τ₂ ]⇒ τ₃) = begin
    cpsT𝑘 (dsT τ) ⇒[ cpsT𝑘 (dsT τ₁) ⇒ cpsT𝑘 (dsT τ₂) ]⇒ cpsT𝑘 (dsT τ₃)
  ≡⟨ cong (λ x → x ⇒[ cpsT𝑘 (dsT τ₁) ⇒ cpsT𝑘 (dsT τ₂) ]⇒ cpsT𝑘 (dsT τ₃))
          (cpsT𝑘∘dsT≡id τ) ⟩
    τ ⇒[ cpsT𝑘 (dsT τ₁) ⇒ cpsT𝑘 (dsT τ₂) ]⇒ cpsT𝑘 (dsT τ₃)
  ≡⟨ cong (λ x → τ ⇒[ x ⇒ cpsT𝑘 (dsT τ₂) ]⇒ cpsT𝑘 (dsT τ₃))
          (cpsT𝑘∘dsT≡id τ₁) ⟩
    (τ ⇒[ τ₁ ⇒ cpsT𝑘 (dsT τ₂) ]⇒ cpsT𝑘 (dsT τ₃))
  ≡⟨ cong (λ x → τ ⇒[ τ₁ ⇒ x ]⇒ cpsT𝑘 (dsT τ₃))
          (cpsT𝑘∘dsT≡id τ₂) ⟩
    (τ ⇒[ τ₁ ⇒ τ₂ ]⇒ cpsT𝑘 (dsT τ₃))
  ≡⟨ cong (λ x → τ ⇒[ τ₁ ⇒ τ₂ ]⇒ x)
          (cpsT𝑘∘dsT≡id τ₃) ⟩
    (τ ⇒[ τ₁ ⇒ τ₂ ]⇒ τ₃)
  ∎
  where open ≡-Reasoning

cpsT𝑘𝑐∘dsT𝑐≡id : (τ : conttyp) → cpsT𝑘𝑐 (dsT𝑐 τ) ≡ τ
cpsT𝑘𝑐∘dsT𝑐≡id (τ₂ ⇒ τ₁) =
  cong₂ _⇒_ (cpsT𝑘∘dsT≡id τ₂) (cpsT𝑘∘dsT≡id τ₁)

postulate
  extensionality : {a b : Level} → Extensionality a b

{-# REWRITE cpsT𝑘∘dsT≡id cpsT𝑘𝑐∘dsT𝑐≡id #-}
mutual
  Right-InvV : {var : cpstyp → Set} {cvar : conttyp → Set} → {τ₁ : cpstyp} →
               (v : cpsvalue𝑐[ var , cvar ] τ₁) →
               cpsV𝑘 (dsV𝑐 v) ≡ v
  Right-InvV (CPSVar x) = refl
  Right-InvV (CPSNum n) = refl
  Right-InvV (CPSFun e) =
    cong CPSFun (extensionality (λ x → extensionality (λ k →
      Right-InvE (e x k))))
  Right-InvV CPSShift = refl

  Right-InvE : {var : cpstyp → Set} {cvar : conttyp → Set} → {τ : cpstyp} →
               (e : cpsterm𝑐[ var , cvar ] τ) →
               cpsE𝑘 (dsE𝑐 e) ≡ e
  Right-InvE (CPSRet k v) = cong₂ CPSRet (Right-InvC k) (Right-InvV v)
  Right-InvE (CPSApp v w k) = begin
      CPSApp (cpsV𝑘 (dsV𝑐 v)) (cpsV𝑘 {τ₁ = dsT _} (dsV𝑐 w))
             (cpsC𝑘 {τ₁ = dsT _} {τ₂ = dsT _} (dsC𝑐 k))
    ≡⟨ cong (CPSApp _ _) (Right-InvC k) ⟩
      CPSApp (cpsV𝑘 (dsV𝑐 v)) (cpsV𝑘 {τ₁ = dsT _} (dsV𝑐 w))
             k
    ≡⟨ cong (λ x → x k) (cong₂ CPSApp (Right-InvV v) (Right-InvV w)) ⟩
      CPSApp v w k
    ∎
    where open ≡-Reasoning
  Right-InvE (CPSRetE k e) = cong₂ CPSRetE (Right-InvC k) (Right-InvE e)

  Right-InvC : {var : cpstyp → Set} {cvar : conttyp → Set} {τ₁ τ₂ : cpstyp} →
               (k : cpscont𝑐[ var , cvar ] (τ₁ ⇒ τ₂)) →
               cpsC𝑘 (dsC𝑐 k) ≡ k
  Right-InvC (CPSKVar k) = refl
  Right-InvC CPSId = refl
  Right-InvC (CPSCont e) =
    cong CPSCont (extensionality (λ x → Right-InvE (e x)))
