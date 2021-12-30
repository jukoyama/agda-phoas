{-# OPTIONS --rewriting #-}

module Lemma_Right_Inv where

open import DStermK hiding (_⇒_cps[_])
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
postulate
  extensionality : {a b : Level} → Extensionality a b

{-# REWRITE cpsT𝑘∘dsT≡id #-}
mutual 
  Right-InvR : {var : cpstyp → Set} → {τ₁ τ₂ τ₃ : cpstyp} →
               (r : (var (τ₁ ⇒[ (τ₂ ⇒ τ₂) ]⇒ τ₂) → cpsterm𝑐[ var ] (τ₂ ⇒ τ₂) τ₃)) →
               cpsMain𝑘 (dsT τ₁) (dsT τ₂) (dsT τ₃) (dsMain𝑐 τ₁ τ₂ τ₃ r)
               ≡
               r
  Right-InvR {var} {τ₁} {τ₂} {τ₃} r =
    begin
      cpsMain𝑘 (dsT τ₁) (dsT τ₂) (dsT τ₃) (dsMain𝑐 τ₁ τ₂ τ₃ r)
    ≡⟨ refl ⟩
      (λ k → cpsE𝑘 (dsT τ₃) (dsT τ₂) (dsE𝑐 τ₃ τ₂ (r k)))
    ≡⟨ extensionality (λ k → Right-InvE (r k)) ⟩
      (λ k → r k)
    ∎
    where open ≡-Reasoning          

  Right-InvE : {var : cpstyp → Set} → {τ₃ τ₅ : cpstyp} →
               (e : cpsterm𝑐[ var ] (τ₅ ⇒ τ₅) τ₃) →
               cpsE𝑘 (dsT τ₃) (dsT τ₅) (dsE𝑐 τ₃ τ₅ e)
               ≡
               e
  Right-InvE {var} {τ₃} {τ₅} (CPSRet {τ₁ = τ₁} {τ₂ = .τ₃} {τ₃ = .τ₅} k v) =
    begin
      cpsE𝑘 (dsT τ₃) (dsT τ₅) (dsE𝑐 τ₃ τ₅ (CPSRet k v))
    ≡⟨ refl ⟩
      CPSRet
        (cpsC𝑘 (dsT τ₁) (dsT τ₃) (dsT τ₃) (dsT τ₅) (dsC𝑐 τ₁ τ₃ τ₃ τ₅ k))
        (cpsV𝑘 (dsT τ₁) (dsV𝑐 τ₁ v))
    ≡⟨ cong₂ CPSRet (Right-InvC k) (Right-InvV v) ⟩
      CPSRet k v
    ∎
    where open ≡-Reasoning          

  Right-InvE {var} {τ₃} {τ₅}
             (CPSApp {τ₁ = τ₁} {τ₂ = τ₂} {τ₃ = τ₄} {τ₄ = .τ₃} {τ₅ = .τ₅}
                     v w k) =
    begin
      cpsE𝑘 (dsT τ₃) (dsT τ₅) (dsE𝑐 τ₃ τ₅ (CPSApp v w k))
    ≡⟨ refl ⟩
      CPSApp
        (cpsV𝑘 (dsT τ₂ ⇒ dsT τ₁ cps[ dsT τ₄ , dsT τ₃ ])
               (dsV𝑐 (τ₂ ⇒[ τ₁ ⇒ τ₄ ]⇒ τ₃) v))
        (cpsV𝑘 (dsT τ₂) (dsV𝑐 τ₂ w))
        (cpsC𝑘 (dsT τ₁) (dsT τ₄) (dsT τ₃) (dsT τ₅) (dsC𝑐 τ₁ τ₄ τ₃ τ₅ k))
    ≡⟨ cong₂ (λ x y → CPSApp x y
                             (cpsC𝑘 (dsT τ₁) (dsT τ₄) (dsT τ₃) (dsT τ₅)
                                    (dsC𝑐 τ₁ τ₄ τ₃ τ₅ k)))
             (Right-InvV v) (Right-InvV w) ⟩
      CPSApp v w
             (cpsC𝑘 (dsT τ₁) (dsT τ₄) (dsT τ₃) (dsT τ₅) (dsC𝑐 τ₁ τ₄ τ₃ τ₅ k))
    ≡⟨ cong (CPSApp v w) (Right-InvC k) ⟩
      CPSApp v w k
    ∎
    where open ≡-Reasoning          

  Right-InvE {var} {τ₃} {τ₅}
             (CPSRetE {τ₀ = τ₀} {τ₁ = τ₁} {τ₂ = .τ₃} {τ₃ = .τ₅} k e) =
    begin
      cpsE𝑘 (dsT τ₃) (dsT τ₅) (dsE𝑐 τ₃ τ₅ (CPSRetE k e))
    ≡⟨ refl ⟩
      CPSRetE
        (cpsC𝑘 (dsT τ₁) (dsT τ₃) (dsT τ₃) (dsT τ₅) (dsC𝑐 τ₁ τ₃ τ₃ τ₅ k))
        (cpsE𝑘 (dsT τ₁) (dsT τ₀) (dsE𝑐 τ₁ τ₀ e))
    ≡⟨ cong₂ CPSRetE (Right-InvC k) (Right-InvE e) ⟩
      CPSRetE k e
    ∎
    where open ≡-Reasoning          

  Right-InvV : {var : cpstyp → Set} → {τ₁ : cpstyp} →
               (v : cpsvalue𝑐[ var ] τ₁) →
               cpsV𝑘 (dsT τ₁) (dsV𝑐 τ₁ v)
               ≡
               v
  Right-InvV {var} {τ₁} (CPSVar {τ₁ = .τ₁} v) = refl
  Right-InvV {var} {.Nat} (CPSNum n) = refl
  Right-InvV {var} {.(τ₂ ⇒[ τ₁ ⇒ τ₃ ]⇒ τ₄)}
             (CPSFun {τ₁ = τ₁} {τ₂ = τ₂} {τ₃ = τ₃} {τ₄ = τ₄} r) =
    begin
      cpsV𝑘 (dsT (τ₂ ⇒[ τ₁ ⇒ τ₃ ]⇒ τ₄))
            (dsV𝑐 (τ₂ ⇒[ τ₁ ⇒ τ₃ ]⇒ τ₄) (CPSFun r))
    ≡⟨ refl ⟩
      CPSFun (λ x k → cpsE𝑘 (dsT τ₄) (dsT τ₃) (dsE𝑐 τ₄ τ₃ (r x k)))
    ≡⟨ cong CPSFun (extensionality (λ x → Right-InvR (r x))) ⟩
      CPSFun r
    ∎
    where open ≡-Reasoning          

  Right-InvV {var} {.(((τ₁ ⇒[ τ₂ ⇒ τ₃ ]⇒ τ₃) ⇒[ τ₄ ⇒ τ₄ ]⇒ τ₅) ⇒[ τ₁ ⇒ τ₂ ]⇒ τ₅)} (CPSShift {τ₁ = τ₁} {τ₂ = τ₂} {τ₃ = τ₃} {τ₄ = τ₄} {τ₅ = τ₅}) = refl

  Right-InvC : {var : cpstyp → Set} → {τ₁ τ₂ τ₃ τ₅ : cpstyp} →
               (k : cpscont𝑐[ var ] (τ₅ ⇒ τ₅) τ₃ (τ₁ ⇒ τ₂)) →
               cpsC𝑘 (dsT τ₁) (dsT τ₂) (dsT τ₃) (dsT τ₅)
                     (dsC𝑐 τ₁ τ₂ τ₃ τ₅ k)
               ≡
               k
  Right-InvC {var} {τ₁} {τ₂} {τ₃} {.τ₂}
             (CPSKVar {τ₁ = .τ₁} {τ₂ = .τ₂} {τ₃ = .τ₃} k) = refl
  Right-InvC {var} {τ₁} {.τ₁} {τ₃} {.τ₁}
             (CPSId {τ₁ = .τ₁} {τ₃ = .τ₃}) = refl
  Right-InvC {var} {τ₁} {τ₂} {τ₃} {τ₅}
             (CPSCont {τ₁ = .τ₁} {τ₂ = .τ₂} {τ₃ = .τ₃} {τ₄ = .τ₅} e) =
    begin
      cpsC𝑘 (dsT τ₁) (dsT τ₂) (dsT τ₃) (dsT τ₅)
            (dsC𝑐 τ₁ τ₂ τ₃ τ₅ (CPSCont e))
    ≡⟨ refl ⟩
      CPSCont (λ x → cpsE𝑘 (dsT τ₂) (dsT τ₅) (dsE𝑐 τ₂ τ₅ (e x)))
    ≡⟨ cong CPSCont (extensionality (λ x → Right-InvE (e x))) ⟩
      CPSCont e
    ∎
    where open ≡-Reasoning          

