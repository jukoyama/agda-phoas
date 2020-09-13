module lemma2 where

open import DSterm
open import CPSterm
open import lemma1

open import Function
open import Relation.Binary.PropositionalEquality

-- @ [e]′ (λv.@'κ v) ⟶* @' [e] κ
cpsEtaEta′ : {var : cpstyp → Set} → {τ₁ τ₂ τ₃ : typ} →
             (e   : term[ var ∘ cpsT ] τ₁ cps[ τ₂ , τ₃ ]) →
             (κ  : cpsvalue[ var ] (cpsT τ₁) → cpsterm[ var ] (cpsT τ₂)) →
             schematicV κ → 
             cpsequal (cpsI′ τ₁ τ₂ τ₃ e (CPSFun (λ a → κ (CPSVar a)))) (cpsI τ₁ τ₂ τ₃ e κ)
             
cpsEtaEta′ {τ₁ = τ₁} {τ₂} {.τ₂} (Val {τ₁ = .τ₁} {τ₂ = .τ₂} v) κ sche =
  begin
    cpsI′ τ₁ τ₂ τ₂ (Val v) (CPSFun (λ a → κ (CPSVar a)))
  ≡⟨ refl ⟩
    CPSApp (CPSVal (CPSFun (λ a → κ (CPSVar a))))
           (CPSVal (cpsV τ₁ v))    
  ⟶⟨ eqBeta (sche v) ⟩
    κ (cpsV τ₁ v)
  ⟶⟨ eqId ⟩
    cpsI τ₁ τ₂ τ₂ (Val v) κ
  ∎

cpsEtaEta′ {τ₁ = τ₁} {τ₂} {τ₃} (App {τ₁ = .τ₁} {τ₂ = τ₄} {τ₃ = .τ₂} {τ₄ = τ₅} {τ₅ = τ₆} {τ₆ = .τ₃} e₁ e₂) κ sche =
  begin
    cpsI′ τ₁ τ₂ τ₃ (App e₁ e₂) (CPSFun (λ a → κ (CPSVar a)))
  ≡⟨ refl ⟩
    cpsI (τ₄ ⇒ τ₁ cps[ τ₂ , τ₅ ]) τ₆ τ₃ e₁
    (λ m → cpsI τ₄ τ₅ τ₆ e₂
           λ n → CPSApp (CPSApp (CPSVal m) (CPSVal n)) (CPSVal (CPSFun (λ a → κ (CPSVar a)))))
  ⟶⟨ eqId ⟩
    cpsI τ₁ τ₂ τ₃ (App e₁ e₂) κ
  ∎
  
cpsEtaEta′ {τ₁ = .τ₂} {.τ₃} {.τ₃} (Reset τ₁ τ₂ τ₃ e) κ sche =
  begin
    cpsI′ τ₂ τ₃ τ₃ (Reset τ₁ τ₂ τ₃ e) (CPSFun (λ a → κ (CPSVar a)))
  ≡⟨ refl ⟩
    CPSLet (cpsI τ₁ τ₁ τ₂ e (λ m → CPSVal m))
           (λ c → CPSApp (CPSVal (CPSFun λ a → κ (CPSVar a))) (CPSVal (CPSVar c)))
  ⟶⟨ eqLet₂ (cpsI τ₁ τ₁ τ₂ e CPSVal) (λ k' → eqBeta (sche (Var k'))) ⟩
    CPSLet (cpsI τ₁ τ₁ τ₂ e (λ m → CPSVal m))
           (λ c → κ (CPSVar c))
  ⟶⟨ eqId ⟩
    cpsI τ₂ τ₃ τ₃ (Reset τ₁ τ₂ τ₃ e) κ
  ∎

cpsEtaEta′ {τ₁ = .τ₃} {.τ₄} {.τ₂} (Shift τ τ₁ τ₂ τ₃ τ₄ e) κ sche =
  begin
    cpsI′ τ₃ τ₄ τ₂ (Shift τ τ₁ τ₂ τ₃ τ₄ e) (CPSFun (λ a → κ (CPSVar a)))
  ≡⟨ refl ⟩
    CPSLet (CPSVal (CPSFun (λ a → CPSVal (CPSFun
           (λ κ′ → CPSApp (CPSVal (CPSVar κ′))
                           (CPSApp (CPSVal (CPSFun (λ a → κ (CPSVar a)))) -- ????
                                   (CPSVal (CPSVar a))))))))
      (λ c → cpsI τ₁ τ₁ τ₂ (e c) (λ m → CPSVal m))
  ⟶⟨ eqLet₁ (λ c → cpsI τ₁ τ₁ τ₂ (e c) (λ m → CPSVal m))
      (eqFun λ a → eqFun (λ κ′ → eqApp₂ (eqBeta (sche (Var a)))) ) ⟩
    CPSLet (CPSVal (CPSFun (λ a → CPSVal (CPSFun
           (λ κ′ → CPSApp (CPSVal (CPSVar κ′)) (κ (CPSVar a)))))))
      (λ c → cpsI τ₁ τ₁ τ₂ (e c) (λ m → CPSVal m))
  ⟶⟨ eqId ⟩
    cpsI τ₃ τ₄ τ₂ (Shift τ τ₁ τ₂ τ₃ τ₄ e) κ
  ∎
