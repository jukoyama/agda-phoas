module lemma4 where

open import DSterm
open import CPSterm
open import lemma1
open import lemma2

open import Function
open import Relation.Binary.PropositionalEquality

contextContE : {var : cpstyp → Set} → {τ τ₀ τ₁ τ₂ τ₃ τ₄ τ₅ : typ} →
               (v : value[ var ∘ cpsT ] (τ₃ ⇒ τ₄ cps[ τ , τ ]) ⇒ τ₁ cps[ τ₁ , τ ] cps[τ,τ]) →
               (κ : cpsvalue[ var ] (cpsT τ₂) → cpsterm[ var ] (cpsT τ₅)) →
               (p₁ : pcontext[ var ∘ cpsT , τ₃ cps[ τ₄ , τ ]] τ₂ cps[ τ₅ , τ ]) →
               (p₂ : pcontext[ var ∘ cpsT , τ₃ cps[ τ₀ , τ₀ ]] τ₂ cps[ τ₅ , τ₄ ]) →
               same-pcontext p₁ p₂ →
               schematic κ →
               cpsequal (cpsI τ₂ τ₅ τ (pcontext-plug p₁ (NonVal (App (Val Shift) (Val v)))) κ)
                        (cpsI′ τ₃ τ₄ τ (NonVal (App (Val Shift) (Val v)))
                                (CPSFun λ a → cpsI τ₂ τ₅ τ₄ (pcontext-plug p₂ (Val (Var a))) κ))
contextContE {var} {τ} {τ₀} {τ₁} {τ₂} {.τ₂} {.τ₀} {.τ₀} v κ
              .(Hole {_} {τ₂} {τ₀} {τ})
              .(Hole {_} {τ₂} {τ₀} {τ₀})
              (Hole {τ₁ = .τ₂} {τ₁' = .τ₂} {τ₂ = .τ₀} {τ₂' = .τ₀} {τ₃ = .τ} {τ₃' = .τ₀})
              sche =
  begin
    cpsI τ₂ τ₀ τ
      (pcontext-plug Hole (NonVal (App (Val Shift) (Val v)))) κ
  ≡⟨ refl ⟩
    cpsI (((τ₂ ⇒ τ₀ cps[ τ , τ ]) ⇒ τ₁ cps[ τ₁ , τ ]) ⇒ τ₂ cps[ τ₀ , τ ]) τ τ (Val Shift)
         (λ m → cpsI ((τ₂ ⇒ τ₀ cps[ τ , τ ]) ⇒ τ₁ cps[ τ₁ , τ ]) τ τ (Val v)
                (λ n → CPSApp (CPSApp (CPSVal m) (CPSVal n)) (CPSVal (CPSFun (λ a → κ (CPSVar a))))))
  ≡⟨ refl ⟩
    cpsI′ τ₂ τ₀ τ (NonVal (App (Val Shift) (Val v))) (CPSFun (λ a → κ (CPSVar a)))
  ≡⟨ refl ⟩
    cpsI′ τ₂ τ₀ τ (NonVal (App (Val Shift) (Val v)))
          (CPSFun (λ a → cpsI τ₂ τ₀ τ₀ (Val (Var a)) κ))    
  ≡⟨ refl ⟩
    cpsI τ₂ τ₀ τ
      (pcontext-plug Hole (NonVal (App (Val Shift) (Val v)))) κ
  ∎

contextContE {var} {τ} {τ₀} {τ₁} {τ₂} {τ₃} {τ₄} {τ₅} v κ
              .(Frame {_} {τ₃} {τ₄} {τ} {τ₆ ⇒ τ₂ cps[ τ₅ , τ₈ ]} {τ₇} {τ} {τ₂} {τ₅} {τ}
                      (App₁ {_} {τ₂} {τ₆} {τ₅} {τ₈} {τ₇} {τ} e₂) p₁)
              .(Frame {_} {τ₃} {τ₀} {τ₀} {τ₆ ⇒ τ₂ cps[ τ₅ , τ₈ ]} {τ₇} {τ₄} {τ₂} {τ₅} {τ₄}
                      (App₁ {_} {τ₂} {τ₆} {τ₅} {τ₈} {τ₇} {τ₄} e₂) p₂)
              (Frame {τ₁ = .τ₃} {τ₁' = .τ₃} {τ₂ = .τ₄} {τ₂' = .τ₀} {τ₃ = .τ} {τ₃' = .τ₀}
                     {τ₄ = .(τ₆ ⇒ τ₂ cps[ τ₅ , τ₈ ])} {τ₄' = .(τ₆ ⇒ τ₂ cps[ τ₅ , τ₈ ])}
                     {τ₅ = τ₇} {τ₅' = .τ₇} {τ₆ = .τ} {τ₆' = .τ₄} {τ₇ = .τ₂} {τ₇' = .τ₂}
                     {τ₈ = .τ₅} {τ₈' = .τ₅} {τ₉ = .τ} {τ₉' = .τ₄}
                     {f₁ = App₁ {τ₁ = .τ₂} {τ₂ = τ₆} {τ₃ = .τ₅} {τ₄ = τ₈} {τ₅ = .τ₇} {τ₆ = .τ} e₂}
                     {f₂ = App₁ {τ₁ = .τ₂} {τ₂ = .τ₆} {τ₃ = .τ₅} {τ₄ = .τ₈} {τ₅ = .τ₇} {τ₆ = .τ₄} .e₂}
             (App₁ {τ₇ = .τ₆} {τ₈ = .τ₈} {τ₉ = .τ₇} {τ₃ = .τ} {τ₃' = .τ₄}
                   {τ₄ = .τ₂} {τ₄' = .τ₂} {τ₅ = .τ₅} {τ₅' = .τ₅} .e₂) {p₁ = p₁} {p₂ = p₂} same-con) sche =
  begin
    cpsI τ₂ τ₅ τ
         (pcontext-plug (Frame (App₁ e₂) p₁) (NonVal (App (Val Shift) (Val v)))) κ
  ≡⟨ refl ⟩
    cpsI τ₂ τ₅ τ
         (pframe-plug (App₁ e₂) (pcontext-plug p₁ (NonVal (App (Val Shift) (Val v))))) κ
  ≡⟨ refl ⟩
    cpsI τ₂ τ₅ τ
         (NonVal (App (pcontext-plug p₁ (NonVal (App (Val Shift) (Val v)))) e₂)) κ
  ≡⟨ refl ⟩
    cpsI (τ₆ ⇒ τ₂ cps[ τ₅ , τ₈ ]) τ₇ τ (pcontext-plug p₁ (NonVal (App (Val Shift) (Val v))))
         (λ m → cpsI τ₆ τ₈ τ₇ e₂
         (λ n → CPSApp (CPSApp (CPSVal m) (CPSVal n)) (CPSVal (CPSFun (λ a → κ (CPSVar a))))))
  ⟶⟨ contextContE v (λ m → cpsI τ₆ τ₈ τ₇ e₂
                             (λ n → CPSApp (CPSApp (CPSVal m) (CPSVal n)) (CPSVal (CPSFun (λ a → κ (CPSVar a))))))
                   p₁ p₂ same-con
                   (λ v₁ → κSubst e₂
                               (λ m n → CPSApp (CPSApp (CPSVal m) (CPSVal n))
                                                (CPSVal (CPSFun λ a → κ (CPSVar a))))
                               λ x → sApp (sApp (sVal sVar=) Subst≠) Subst≠) ⟩
    cpsI′ τ₃ τ₄ τ (NonVal (App (Val Shift) (Val v)))
          (CPSFun (λ a′ → cpsI (τ₆ ⇒ τ₂ cps[ τ₅ , τ₈ ]) τ₇ τ₄ (pcontext-plug p₂ (Val (Var a′)))
                  (λ m → cpsI τ₆ τ₈ τ₇ e₂
                  (λ n → CPSApp (CPSApp (CPSVal m) (CPSVal n)) (CPSVal (CPSFun (λ a → κ (CPSVar a))))))))
  ≡⟨ refl ⟩
     cpsI′ τ₃ τ₄ τ (NonVal (App (Val Shift) (Val v)))
           (CPSFun (λ a → cpsI τ₂ τ₅ τ₄
                   (NonVal (App (pcontext-plug p₂ (Val (Var a))) e₂)) κ))
  ≡⟨ refl ⟩
    cpsI′ τ₃ τ₄ τ (NonVal (App (Val Shift) (Val v)))
          (CPSFun (λ a → cpsI τ₂ τ₅ τ₄ (pcontext-plug (Frame (App₁ e₂) p₂) (Val (Var a))) κ))
  ∎
                     
contextContE {var} {τ} {τ₀} {τ₁} {τ₂} {τ₃} {τ₄} {τ₅} v κ
              .(Frame {_} {τ₃} {τ₄} {τ} {τ₆} {τ₇} {τ} {τ₂} {τ₅} {τ}
                      (App₂ {_} {τ₂} {τ₆} {τ₅} {τ₇} {τ} v₁) p₁)
              .(Frame {_} {τ₃} {τ₀} {τ₀} {τ₆} {τ₇} {τ₄} {τ₂} {τ₅} {τ₄}
                      (App₂ {_} {τ₂} {τ₆} {τ₅} {τ₇} {τ₄} v₁) p₂)
              (Frame {τ₁ = .τ₃} {τ₁' = .τ₃} {τ₂ = .τ₄} {τ₂' = .τ₀} {τ₃ = .τ} {τ₃' = .τ₀}
                     {τ₄ = τ₆} {τ₄' = .τ₆} {τ₅ = τ₇} {τ₅' = .τ₇} {τ₆ = .τ} {τ₆' = .τ₄}
                     {τ₇ = .τ₂} {τ₇' = .τ₂} {τ₈ = .τ₅} {τ₈' = .τ₅} {τ₉ = .τ} {τ₉' = .τ₄}
                     {f₁ = App₂ {τ₁ = .τ₂} {τ₂ = .τ₆} {τ₃ = .τ₅} {τ₄ = .τ₇} {τ₅ = .τ} v₁}
                     {f₂ = App₂ {τ₁ = .τ₂} {τ₂ = .τ₆} {τ₃ = .τ₅} {τ₄ = .τ₇} {τ₅ = .τ₄} .v₁}
              (App₂  {τ₇ = .τ₂} {τ₈ = .τ₆} {τ₉ = .τ₅} {τ₁₀ = .τ₇} {τ₃ = .τ} {τ₃' = .τ₄} .v₁)
                     {p₁ = p₁} {p₂ = p₂} same-con) sche =
  begin
    cpsI τ₂ τ₅ τ
      (pcontext-plug (Frame (App₂ v₁) p₁) (NonVal (App (Val Shift) (Val v)))) κ
  ≡⟨ refl ⟩
    cpsI τ₂ τ₅ τ
      (pframe-plug (App₂ v₁) (pcontext-plug p₁ (NonVal (App (Val Shift) (Val v))))) κ
  ≡⟨ refl ⟩
    cpsI τ₂ τ₅ τ
      (NonVal (App (Val v₁) (pcontext-plug p₁ (NonVal (App (Val Shift) (Val v)))))) κ
  ≡⟨ refl ⟩
    cpsI (τ₆ ⇒ τ₂ cps[ τ₅ , τ₇ ]) τ τ (Val v₁)
         (λ m → cpsI τ₆ τ₇ τ (pcontext-plug p₁ (NonVal (App (Val Shift) (Val v))))
         (λ n → CPSApp (CPSApp (CPSVal m) (CPSVal n)) (CPSVal (CPSFun (λ a → κ (CPSVar a))))))
  ≡⟨ refl ⟩
    cpsI τ₆ τ₇ τ (pcontext-plug p₁ (NonVal (App (Val Shift) (Val v))))
         (λ n → CPSApp (CPSApp (CPSVal (cpsV (τ₆ ⇒ τ₂ cps[ τ₅ , τ₇ ]) v₁)) (CPSVal n)) (CPSVal (CPSFun (λ a → κ (CPSVar a)))))
  ⟶⟨ contextContE v
         (λ n → CPSApp (CPSApp (CPSVal (cpsV (τ₆ ⇒ τ₂ cps[ τ₅ , τ₇ ]) v₁)) (CPSVal n)) (CPSVal (CPSFun (λ a → κ (CPSVar a)))))
         p₁ p₂ same-con
         (λ v₂ → sApp (sApp Subst≠ (sVal sVar=)) Subst≠) ⟩
    cpsI′ τ₃ τ₄ τ (NonVal (App (Val Shift) (Val v)))
          (CPSFun (λ a → cpsI τ₆ τ₇ τ₄ (pcontext-plug p₂ (Val (Var a)))
                  λ n →
                    CPSApp
                      (CPSApp (CPSVal (cpsV (τ₆ ⇒ τ₂ cps[ τ₅ , τ₇ ]) v₁)) (CPSVal n))
                      (CPSVal (CPSFun (λ a → κ (CPSVar a))))))
  ≡⟨ refl ⟩
    cpsI′ τ₃ τ₄ τ (NonVal (App (Val Shift) (Val v)))
          (CPSFun (λ a → cpsI (τ₆ ⇒ τ₂ cps[ τ₅ , τ₇ ]) τ₄ τ₄ (Val v₁)
            (λ m → cpsI τ₆ τ₇ τ₄ (pcontext-plug p₂ (Val (Var a)))
            (λ n → CPSApp (CPSApp (CPSVal m) (CPSVal n)) (CPSVal (CPSFun (λ a → κ (CPSVar a))))))))
  ≡⟨ refl ⟩
    cpsI′ τ₃ τ₄ τ (NonVal (App (Val Shift) (Val v)))
          (CPSFun (λ a →
            cpsI τ₂ τ₅ τ₄ (NonVal (App (Val v₁) (pcontext-plug p₂ (Val (Var a))))) κ))
  ≡⟨ refl ⟩
    cpsI′ τ₃ τ₄ τ (NonVal (App (Val Shift) (Val v)))
          (CPSFun (λ a → cpsI τ₂ τ₅ τ₄ (pcontext-plug (Frame (App₂ v₁) p₂) (Val (Var a))) κ))
  ∎


contextContE {var} {τ} {τ₀} {τ₁} {τ₂} {τ₃} {τ₄} {τ₅} v κ
              .(Frame {_} {τ₃} {τ₄} {τ} {τ₆} {τ₇} {τ} {τ₂} {τ₅} {τ}
                      (Let {_} {τ₆} {τ₂} {τ₅} {τ₇} {τ} e₂) p₁)
              .(Frame {_} {τ₃} {τ₀} {τ₀} {τ₆} {τ₇} {τ₄} {τ₂} {τ₅} {τ₄}
                      (Let {_} {τ₆} {τ₂} {τ₅} {τ₇} {τ₄} e₂) p₂)
              (Frame  {τ₁ = .τ₃} {τ₁' = .τ₃} {τ₂ = .τ₄} {τ₂' = .τ₀} {τ₃ = .τ}
                      {τ₃' = .τ₀} {τ₄ = τ₆} {τ₄' = .τ₆} {τ₅ = τ₇} {τ₅' = .τ₇}
                      {τ₆ = .τ} {τ₆' = .τ₄} {τ₇ = .τ₂} {τ₇' = .τ₂} {τ₈ = .τ₅}
                      {τ₈' = .τ₅} {τ₉ = .τ} {τ₉' = .τ₄}
                      {f₁ = Let {τ₁ = .τ₆} {τ₂ = .τ₂} {α = .τ₅} {β = .τ₇} {γ = .τ} e₂}
                      {f₂ = Let {τ₁ = .τ₆} {τ₂ = .τ₂} {α = .τ₅} {β = .τ₇} {γ = .τ₄} .e₂}
             (Let {τ₇ = .τ₂} {τ₈ = .τ₆} {τ₉ = .τ₅} {τ₁₀ = .τ₇} {τ₃ = .τ} {τ₃' = .τ₄} .e₂)
                  {p₁ = p₁} {p₂ = p₂} same-con) sche =
  begin
    cpsI τ₂ τ₅ τ
      (pcontext-plug (Frame (Let e₂) p₁) (NonVal (App (Val Shift) (Val v)))) κ
  ≡⟨ refl ⟩
    cpsI τ₂ τ₅ τ
      (pframe-plug (Let e₂) (pcontext-plug p₁ (NonVal (App (Val Shift) (Val v))))) κ
  ≡⟨ refl ⟩
    cpsI τ₂ τ₅ τ
         (NonVal (Let (pcontext-plug p₁ (NonVal (App (Val Shift) (Val v)))) e₂)) κ
  ≡⟨ refl ⟩
    cpsI τ₆ τ₇ τ (pcontext-plug p₁ (NonVal (App (Val Shift) (Val v))))
         (λ m → CPSLet (CPSVal m) (λ x → cpsI τ₂ τ₅ τ₇ (e₂ x) κ))
  ⟶⟨ contextContE v
        (λ m → CPSLet (CPSVal m) (λ x → cpsI τ₂ τ₅ τ₇ (e₂ x) κ))
        p₁ p₂ same-con
        (λ v₁ → sLet (λ x → Subst≠) (λ x → sVal sVar=)) ⟩
    cpsI′ τ₃ τ₄ τ (NonVal (App (Val Shift) (Val v)))
          (CPSFun (λ a → cpsI τ₂ τ₅ τ₄
                               (NonVal (Let (pcontext-plug p₂ (Val (Var a))) e₂)) κ))
  ≡⟨ refl ⟩
    cpsI′ τ₃ τ₄ τ (NonVal (App (Val Shift) (Val v)))
          (CPSFun (λ a → cpsI τ₂ τ₅ τ₄ (pcontext-plug (Frame (Let e₂) p₂) (Val (Var a))) κ))
  ∎

