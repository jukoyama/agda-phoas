module lemma2 where

open import DSterm
open import CPSterm
open import reasoning
open import lemma1

open import Data.Product
open import Function
open import Relation.Binary.PropositionalEquality


correctCont : {var : cpstyp → Set} → {τ₁ τ₂ τ₃ : typ} →
              {e₁ : term[ var ∘ cpsT ] τ₁ cps[ τ₂ , τ₃ ]} →
              (κ₁ : cpsvalue[ var ] (cpsT τ₁) → cpsterm[ var ] (cpsT τ₂)) →
              (κ₂ : cpsvalue[ var ] (cpsT τ₁) → cpsterm[ var ] (cpsT τ₂)) →
              schematic κ₁ →
              schematic κ₂ →
              ((v : value[ var ∘ cpsT ] τ₁ cps[τ,τ]) →
              cpsequal (κ₁ (cpsV τ₁ v)) (κ₂ (cpsV τ₁ v))) →
              cpsequal (cpsI τ₁ τ₂ τ₃ e₁ κ₁) (cpsI τ₁ τ₂ τ₃ e₁ κ₂)

correctCont {var} {τ₁} {τ₂} {.τ₂} {e₁ = Val {τ₁ = .τ₁} {τ₂ = .τ₂} x} κ₁ κ₂ sche₁ sche₂ eq = eq x

correctCont {var} {τ₁} {τ₂} {τ₃} {e₁ = NonVal {τ₁ = .τ₁} {τ₂ = .τ₂} {τ₃ = .τ₃}
             (App {τ₁ = .τ₁} {τ₂ = τ₄} {τ₃ = .τ₂} {τ₄ = τ₅} {τ₅ = τ₆} {τ₆ = .τ₃} e₁ e₂)} κ₁ κ₂ sche₁ sche₂ eq =
  correctCont {e₁ = e₁}
    (λ m → cpsI τ₄ τ₅ τ₆ e₂
    (λ n →
           CPSApp (CPSApp (CPSVal m) (CPSVal n))
                  (CPSVal (CPSFun (λ a → κ₁ (CPSVar a))))))
    (λ m → cpsI τ₄ τ₅ τ₆ e₂
    (λ n →
           CPSApp (CPSApp (CPSVal m) (CPSVal n))
                  (CPSVal (CPSFun (λ a → κ₂ (CPSVar a))))))
    (λ v₁ v₁′ v sub →
      κSubst e₂ (λ v′ n → CPSApp (CPSApp (CPSVal v′) (CPSVal n)) (CPSVal (CPSFun (λ a → κ₁ (CPSVar a)))))
              (λ x₁ sub₁ → sApp (sApp (sVal sub₁) Subst≠) Subst≠) sub)
    (λ v₁ v₁′ v sub →
      κSubst e₂ (λ v′ n → CPSApp (CPSApp (CPSVal v′) (CPSVal n)) (CPSVal (CPSFun (λ a → κ₂ (CPSVar a)))))
              (λ x₁ sub₁ → sApp (sApp (sVal sub₁) Subst≠) Subst≠) sub)
    λ v →
  correctCont {e₁ = e₂}
    (λ n →
        CPSApp
        (CPSApp (CPSVal (cpsV (τ₄ ⇒ τ₁ cps[ τ₂ , τ₅ ]) v)) (CPSVal n))
        (CPSVal (CPSFun (λ a → κ₁ (CPSVar a)))))
    (λ n →
        CPSApp
        (CPSApp (CPSVal (cpsV (τ₄ ⇒ τ₁ cps[ τ₂ , τ₅ ]) v)) (CPSVal n))
        (CPSVal (CPSFun (λ a → κ₂ (CPSVar a)))))
    (λ v₁ v₁′ v₂ sub → sApp (sApp Subst≠ (sVal sub)) Subst≠)
    (λ v₁ v₁′ v₂ sub → sApp (sApp Subst≠ (sVal sub)) Subst≠)
    λ v₁ → eqApp₂ (eqFun (λ a → eq (Var a)))

correctCont {var} {τ₁} {τ₂} {.τ₂} {e₁ = NonVal {τ₁ = .τ₁} {τ₂ = .τ₂} {τ₃ = .τ₂}
             (Reset τ₃ .τ₁ .τ₂ e)} κ₁ κ₂ sche₁ sche₂ eq =
  eqApp₁ (eqFun (λ m → eq (Var m)))
  
correctCont {var} {τ₁} {τ₂} {τ₃}
            {e₁ = NonVal {τ₁ = .τ₁} {τ₂ = .τ₂} {τ₃ = .τ₃}
                  (Let {τ₁ = τ₄} {τ₂ = .τ₁} {α = .τ₂} {β = β} {γ = .τ₃} e₁ e₂)} κ₁ κ₂ sche₁ sche₂ eq =
  correctCont {e₁ = e₁}
              (λ m → CPSApp (CPSVal (CPSFun (λ c → cpsI τ₁ τ₂ β (e₂ c) κ₁))) (CPSVal m))
              (λ m →
                  CPSApp (CPSVal (CPSFun (λ c → cpsI τ₁ τ₂ β (e₂ c) κ₂))) (CPSVal m))
              (λ v₁ v₁′ v sub → sApp Subst≠ (sVal sub))
              (λ v₁ v₁′ v sub → sApp Subst≠ (sVal sub))
              λ v → eqApp₁ (eqFun (λ c →
  correctCont {e₁ = e₂ c}
              κ₁ κ₂ sche₁ sche₂ λ v₁ → eq v₁))
  
-- @ [e]′ (λv.@'κ v) ⟶* @' [e] κ
cpsEtaEta′ : {var : cpstyp → Set} → {τ₁ τ₂ τ₃ : typ} →
             (e   : term[ var ∘ cpsT ] τ₁ cps[ τ₂ , τ₃ ]) →
             (κ  : cpsvalue[ var ] (cpsT τ₁) → cpsterm[ var ] (cpsT τ₂)) →
             schematic κ → 
             cpsequal (cpsI′ τ₁ τ₂ τ₃ e (CPSFun (λ a → κ (CPSVar a)))) (cpsI τ₁ τ₂ τ₃ e κ)
             
cpsEtaEta′ {τ₁ = τ₁} {τ₂} {.τ₂} (Val {τ₁ = .τ₁} {τ₂ = .τ₂} v) κ sche =
  begin
    cpsI′ τ₁ τ₂ τ₂ (Val v) (CPSFun (λ a → κ (CPSVar a)))
  ≡⟨ refl ⟩
    CPSApp (CPSVal (CPSFun (λ a → κ (CPSVar a))))
           (CPSVal (cpsV τ₁ v))
  ≡⟨ refl ⟩
    CPSApp (CPSVal (CPSFun (λ a → κ (cpsV τ₁ (Var a)))))
           (CPSVal (cpsV τ₁ v))
  ⟶⟨ eqBeta (sche (λ a → CPSVar a) (cpsV τ₁ v) (cpsV τ₁ v) (eSubstV sVar=)) ⟩
    κ (cpsV τ₁ v)
  ⟶⟨ eqId ⟩
    cpsI τ₁ τ₂ τ₂ (Val v) κ
  ∎

cpsEtaEta′ {τ₁ = τ₁} {τ₂} {τ₃} (NonVal (App {τ₁ = .τ₁} {τ₂ = τ₄} {τ₃ = .τ₂} {τ₄ = τ₅} {τ₅ = τ₆} {τ₆ = .τ₃} e₁ e₂)) κ sche =
  begin
    cpsI′ τ₁ τ₂ τ₃ (NonVal (App e₁ e₂)) (CPSFun (λ a → κ (CPSVar a)))
  ≡⟨ refl ⟩
    cpsI (τ₄ ⇒ τ₁ cps[ τ₂ , τ₅ ]) τ₆ τ₃ e₁
    (λ m → cpsI τ₄ τ₅ τ₆ e₂
           λ n → CPSApp (CPSApp (CPSVal m) (CPSVal n)) (CPSVal (CPSFun (λ a → κ (CPSVar a)))))
  ⟶⟨ eqId ⟩
    cpsI τ₁ τ₂ τ₃ (NonVal (App e₁ e₂)) κ
  ∎
  
cpsEtaEta′ {τ₁ = .τ₂} {.τ₃} {.τ₃} (NonVal (Reset τ₁ τ₂ τ₃ e)) κ sche =
  eqId

cpsEtaEta′ {τ₁ = τ₁} {τ₂} {τ₃} (NonVal (Let {τ₁ = τ₄} {τ₂ = .τ₁} {α = .τ₂} {β = β} {γ = .τ₃} e₁ e₂)) κ sche =
  correctCont {e₁ = e₁}
    (λ m →
        CPSApp (CPSVal (CPSFun (λ c → cpsI′ τ₁ τ₂ β (e₂ c) (CPSFun (λ a → κ (CPSVar a))))))
               (CPSVal m))
    (λ m →
        CPSApp (CPSVal (CPSFun (λ c → cpsI τ₁ τ₂ β (e₂ c) κ))) (CPSVal m))
    (λ v₁ v₁′ v sub → sApp Subst≠ (sVal sub))
    (λ v₁ v₁′ v sub → sApp Subst≠ (sVal sub))
    λ v → eqApp₁ (eqFun (λ c → cpsEtaEta′ (e₂ c) κ sche))
