module lemma2 where

open import DSterm
open import CPSterm
open import lemma1

open import Data.Product
open import Function
open import Relation.Binary.PropositionalEquality


correctCont₁ : {var : cpstyp → Set} → {τ₁ τ₂ τ₃ : typ} →
               {e₁ : term[ var ∘ cpsT ] τ₁ cps[ τ₂ , τ₃ ]} →
               (κ₁ : cpsvalue[ var ] (cpsT τ₁) → cpsterm[ var ] (cpsT τ₂)) →
               (κ₂ : cpsvalue[ var ] (cpsT τ₁) → cpsterm[ var ] (cpsT τ₂)) →
               schematic {var} {τ₁} {τ₂} κ₁ →
               schematic {var} {τ₁} {τ₂} κ₂ →
               ((v : value[ var ∘ cpsT ] τ₁ cps[τ,τ]) →
               cpsequal (κ₁ (cpsV τ₁ v)) (κ₂ (cpsV τ₁ v))) →
               cpsequal (cpsI τ₁ τ₂ τ₃ e₁ κ₁) (cpsI τ₁ τ₂ τ₃ e₁ κ₂)
correctCont₁ {var} {τ₁} {τ₂} {.τ₂} {Val {τ₁ = .τ₁} {τ₂ = .τ₂} x} κ₁ κ₂ sche₁ sche₂ eq = eq x
correctCont₁ {var} {τ₁} {τ₂} {τ₃}
             {NonVal (App {τ₁ = .τ₁} {τ₂ = τ₄} {τ₃ = .τ₂} {τ₄ = τ₅} {τ₅ = τ₆} {τ₆ = .τ₃} e₁ e₂)} κ₁ κ₂ sche₁ sche₂ eq =
  begin
    cpsI τ₁ τ₂ τ₃ (NonVal (App e₁ e₂)) κ₁
  ≡⟨ refl ⟩
    cpsI (τ₄ ⇒ τ₁ cps[ τ₂ , τ₅ ]) τ₆ τ₃ e₁
         (λ m → cpsI τ₄ τ₅ τ₆ e₂
                     λ n → CPSApp (CPSApp (CPSVal m) (CPSVal n)) (CPSVal (CPSFun (λ a → κ₁ (CPSVar a)))))
  ⟶⟨ correctCont₁ {e₁ = e₁}
                    (λ m → cpsI τ₄ τ₅ τ₆ e₂
                                (λ n → CPSApp (CPSApp (CPSVal m) (CPSVal n)) (CPSVal (CPSFun (λ a → κ₁ (CPSVar a))))))
                    (λ m → cpsI τ₄ τ₅ τ₆ e₂
                                (λ n → CPSApp (CPSApp (CPSVal m) (CPSVal n)) (CPSVal (CPSFun (λ a → κ₂ (CPSVar a))))))
                    (λ x → κSubst e₂ (λ v → λ n → CPSApp (CPSApp (CPSVal v) (CPSVal n)) (CPSVal (CPSFun (λ a → κ₁ (CPSVar a)))))
                                   λ x₁ → sApp (sApp (sVal sVar=) Subst≠) (sVal (sFun (λ a → Subst≠))))
                    (λ x → κSubst e₂ (λ v → λ n → CPSApp (CPSApp (CPSVal v) (CPSVal n)) (CPSVal (CPSFun (λ a → κ₂ (CPSVar a)))))
                                   λ x₁ → sApp (sApp (sVal sVar=) Subst≠) (sVal (sFun (λ a → Subst≠))))
                    (λ v → correctCont₁ {e₁ = e₂}
                                         (λ n → CPSApp (CPSApp (CPSVal (cpsV (τ₄ ⇒ τ₁ cps[ τ₂ , τ₅ ]) v)) (CPSVal n))
                                                        (CPSVal (CPSFun (λ a → κ₁ (CPSVar a)))))
                                         (λ n → CPSApp (CPSApp (CPSVal (cpsV (τ₄ ⇒ τ₁ cps[ τ₂ , τ₅ ]) v)) (CPSVal n))
                                                        (CPSVal (CPSFun (λ a → κ₂ (CPSVar a)))))
                                         (λ x′ → sApp (sApp (sVal SubstV≠) (sVal sVar=)) (sVal (sFun (λ a → Subst≠))))
                                         (λ x′ → sApp (sApp (sVal SubstV≠) (sVal sVar=)) (sVal (sFun (λ a → Subst≠))))
                                         λ v₁ → eqApp₂ (eqFun (λ a → eq (Var a)))) ⟩                     
    cpsI (τ₄ ⇒ τ₁ cps[ τ₂ , τ₅ ]) τ₆ τ₃ e₁
         (λ m → cpsI τ₄ τ₅ τ₆ e₂
                     (λ n → CPSApp (CPSApp (CPSVal m) (CPSVal n)) (CPSVal (CPSFun (λ a → κ₂ (CPSVar a))))))
  ≡⟨ refl ⟩
    cpsI τ₁ τ₂ τ₃ (NonVal (App e₁ e₂)) κ₂
  ∎
correctCont₁ {var} {.τ₂} {.τ₃} {τ₃} {NonVal (Reset τ₁ τ₂ τ₃ e₁)} κ₁ κ₂ sche₁ sche₂ eq =
  eqLet₂ (cpsI τ₁ τ₁ τ₂ e₁ (λ m → CPSVal m)) (λ x → eq (Var x))

correctCont₁ {var} {τ₁} {τ₂} {τ₃} {NonVal (Let {τ₁ = τ₄} {τ₂ = .τ₁} {α = .τ₂} {β = β} {γ = .τ₃} e₁ e₂)} κ₁ κ₂ sche₁ sche₂ eq =
  begin
    cpsI τ₁ τ₂ τ₃ (NonVal (Let e₁ e₂)) κ₁
  ≡⟨ refl ⟩
    cpsI τ₄ β τ₃ e₁
         (λ m → CPSLet (CPSVal m) (λ c → cpsI τ₁ τ₂ β (e₂ c) κ₁))
  ⟶⟨ correctCont₁ {e₁ = e₁}
          (λ m → CPSLet (CPSVal m) (λ c → cpsI τ₁ τ₂ β (e₂ c) κ₁))
          (λ m → CPSLet (CPSVal m) (λ c → cpsI τ₁ τ₂ β (e₂ c) κ₂))
          (λ v → sLet (λ c → Subst≠) (λ c → sVal sVar=))
          (λ v → sLet (λ c → Subst≠) (λ c → sVal sVar=))
          (λ v → eqLet₂ (CPSVal (cpsV τ₄ v)) λ c → correctCont₁ {e₁ = e₂ c} κ₁ κ₂ sche₁ sche₂ eq) ⟩
    cpsI τ₄ β τ₃ e₁
         (λ m → CPSLet (CPSVal m) (λ c → cpsI τ₁ τ₂ β (e₂ c) κ₂))
  ⟶⟨ eqId ⟩
    cpsI τ₁ τ₂ τ₃ (NonVal (Let e₁ e₂)) κ₂
  ∎

correctContI : {var : cpstyp → Set} → {τ₁ τ₂ τ₃ : typ} →
               {e₁ : term[ var ∘ cpsT ] τ₁ cps[ τ₂ , τ₃ ]} →
               (κ₁ : cpsvalue[ var ] (cpsT τ₁) → cpsterm[ var ] (cpsT τ₂)) →
               (κ₂ : cpsvalue[ var ] (cpsT τ₁) → cpsterm[ var ] (cpsT τ₂)) →
               schematic {var} {τ₁} {τ₂} κ₁ →
               schematic {var} {τ₁} {τ₂} κ₂ →
               ((v : value[ var ∘ cpsT ] τ₁ cps[τ,τ]) →
               cpsRefl (κ₁ (cpsV τ₁ v)) (κ₂ (cpsV τ₁ v))) →
               cpsRefl (cpsI τ₁ τ₂ τ₃ e₁ κ₁) (cpsI τ₁ τ₂ τ₃ e₁ κ₂)
correctContI {e₁ = e₁} κ₁ κ₂ sche₁ sche₂ eq =
  Refl* (correctCont₁ {e₁ = e₁} κ₁ κ₂ sche₁ sche₂ λ v → proj₁ (cpsprod (eq v)))
        (correctCont₁ {e₁ = e₁} κ₂ κ₁ sche₂ sche₁ λ v → proj₂ (cpsprod (eq v)))
  
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
  begin
    cpsI′ τ₂ τ₃ τ₃ (NonVal (Reset τ₁ τ₂ τ₃ e)) (CPSFun (λ a → κ (CPSVar a)))
  ≡⟨ refl ⟩
    CPSLet (cpsI τ₁ τ₁ τ₂ e (λ m → CPSVal m))
           (λ c → CPSApp (CPSVal (CPSFun λ a → κ (CPSVar a))) (CPSVal (CPSVar c)))
  ⟶⟨ eqLet₂ (cpsI τ₁ τ₁ τ₂ e CPSVal) (λ k' → eqBeta (sche (Var k'))) ⟩
    CPSLet (cpsI τ₁ τ₁ τ₂ e (λ m → CPSVal m))
           (λ c → κ (CPSVar c))
  ⟶⟨ eqId ⟩
    cpsI τ₂ τ₃ τ₃ (NonVal (Reset τ₁ τ₂ τ₃ e)) κ
  ∎

cpsEtaEta′ {τ₁ = τ₁} {τ₂} {τ₃} (NonVal (Let {τ₁ = τ₄} {τ₂ = .τ₁} {α = .τ₂} {β = β} {γ = .τ₃} e₁ e₂)) κ sche = 
  begin
    cpsI′ τ₁ τ₂ τ₃ (NonVal (Let e₁ e₂)) (CPSFun (λ a → κ (CPSVar a)))
  ≡⟨ refl ⟩
    cpsI τ₄ β τ₃ e₁
         (λ m → CPSLet (CPSVal m) (λ c → cpsI′ τ₁ τ₂ β (e₂ c) (CPSFun (λ a → κ (CPSVar a)))))
  ⟶⟨ correctCont₁ {e₁ = e₁}
          (λ m → CPSLet (CPSVal m) (λ c → cpsI′ τ₁ τ₂ β (e₂ c) (CPSFun (λ a → κ (CPSVar a)))))
          (λ m → CPSLet (CPSVal m) (λ c → cpsI τ₁ τ₂ β (e₂ c) κ))
          (λ v → sLet (λ c → Subst≠) (λ c → sVal sVar=))
          (λ v → sLet (λ c → Subst≠) (λ c → sVal sVar=))
          (λ v → eqLet₂ (CPSVal (cpsV τ₄ v))
                        (λ c → cpsEtaEta′ (e₂ c) κ sche)) ⟩
     cpsI τ₄ β τ₃ e₁
         (λ m → CPSLet (CPSVal m) (λ c → cpsI τ₁ τ₂ β (e₂ c) κ))
  ⟶⟨ eqId ⟩
    cpsI τ₁ τ₂ τ₃ (NonVal (Let e₁ e₂)) κ
  ∎
