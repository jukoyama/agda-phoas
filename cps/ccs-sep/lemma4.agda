module lemma4 where

open import DSterm
open import CPSterm
open import lemma1
open import lemma2

open import Function
open import Relation.Binary.PropositionalEquality

contextContE : {var : cpstyp → Set} → {τ₁ τ₂ τ₃ τ₄ τ₅ α β γ : typ} →
               (v : value[ (λ x → var (cpsT x)) ] (τ₁ ⇒ τ₂ cps[ α , α ]) ⇒ β cps[ β , τ₃ ] cps[τ,τ]) →
               (κ : cpsvalue[ var ] (cpsT τ₄) → cpsterm[ var ] (cpsT τ₅)) →
               (p₁ : pcontext[ (λ x → var (cpsT x)) , τ₁ cps[ τ₂ , τ₃ ]] τ₄ cps[ τ₅ , τ₃ ]) →
               (p₂ : pcontext[ (λ x → var (cpsT x)) , τ₁ cps[ γ , γ ]] τ₄ cps[ τ₅ , τ₂ ]) →
               same-pcontext p₁ p₂ →
               schematic κ →
               (cpsI τ₄ τ₅ τ₃ (pcontext-plug p₁ (NonVal (App (Val Shift) (Val v)))) κ)
               ≡
               (cpsI′ τ₁ τ₂ τ₃ (NonVal (App (Val Shift) (Val v)))
                      (CPSFun λ a → cpsI τ₄ τ₅ τ₂ (pcontext-plug p₂ (Val (Var a))) κ))

contextContE {var} {τ₁} {τ₂} {τ₃} {.τ₁} {.τ₂} {α} {β} {.τ₂} v κ
             .(Hole {_} {τ₁} {τ₂} {τ₃})
             .(Hole {_} {τ₁} {τ₂} {τ₂})
             (Hole {τ₁ = .τ₁} {τ₁' = .τ₁} {τ₂ = .τ₂} {τ₂' = .τ₂} {τ₃ = .τ₃} {τ₃' = .τ₂}) sche =
  begin
    cpsI τ₁ τ₂ τ₃
      (pcontext-plug Hole (NonVal (App (Val Shift) (Val v)))) κ
  ≡⟨ refl ⟩
    cpsI (((τ₁ ⇒ τ₂ cps[ α , α ]) ⇒ β cps[ β , τ₃ ]) ⇒ τ₁ cps[ τ₂ , τ₃ ]) τ₃ τ₃ (Val Shift)
         (λ m → cpsI ((τ₁ ⇒ τ₂ cps[ α , α ]) ⇒ β cps[ β , τ₃ ]) τ₃ τ₃ (Val v)
                (λ n → CPSApp (CPSApp (CPSVal m) (CPSVal n)) (CPSVal (CPSFun (λ a → κ (CPSVar a))))))
  ≡⟨ refl ⟩
    cpsI′ τ₁ τ₂ τ₃ (NonVal (App (Val Shift) (Val v))) (CPSFun (λ a → κ (CPSVar a)))
  ≡⟨ refl ⟩
    cpsI′ τ₁ τ₂ τ₃ (NonVal (App (Val Shift) (Val v)))
          (CPSFun (λ a → cpsI τ₁ τ₂ τ₂ (Val (Var a)) κ))    
  ≡⟨ refl ⟩
    cpsI τ₁ τ₂ τ₃
      (pcontext-plug Hole (NonVal (App (Val Shift) (Val v)))) κ
  ∎
  where open ≡-Reasoning

contextContE {var} {τ₁} {τ₂} {τ₃} {τ₄} {τ₅} {α} {β} {γ} v κ
             .(Frame {_} {τ₁} {τ₂} {τ₃} {τ₈ ⇒ τ₄ cps[ τ₅ , τ₉ ]} {τ₇} {τ₃} {τ₄} {τ₅} {τ₃}
                     (App₁ {_} {τ₄} {τ₈} {τ₅} {τ₉} {τ₇} {τ₃} e₂) p₁)
             .(Frame {_} {τ₁} {γ} {γ} {τ₈ ⇒ τ₄ cps[ τ₅ , τ₉ ]} {τ₇} {τ₂} {τ₄} {τ₅} {τ₂}
                     (App₁ {_} {τ₄} {τ₈} {τ₅} {τ₉} {τ₇} {τ₂} e₂) p₂)
              (Frame {τ₁ = .τ₁} {τ₁' = .τ₁} {τ₂ = .τ₂} {τ₂' = .γ} {τ₃ = .τ₃} {τ₃' = .γ}
                     {τ₄ = .(τ₈ ⇒ τ₄ cps[ τ₅ , τ₉ ])} {τ₄' = .(τ₈ ⇒ τ₄ cps[ τ₅ , τ₉ ])}
                     {τ₅ = τ₇} {τ₅' = .τ₇} {τ₆ = .τ₃} {τ₆' = .τ₂} {τ₇ = .τ₄} {τ₇' = .τ₄}
                     {τ₈ = .τ₅} {τ₈' = .τ₅} {τ₉ = .τ₃} {τ₉' = .τ₂}
                     {f₁ = .(App₁ {_} {τ₄} {τ₈} {τ₅} {τ₉} {τ₇} {τ₃} e₂)}
                     {f₂ = .(App₁ {_} {τ₄} {τ₈} {τ₅} {τ₉} {τ₇} {τ₂} e₂)}
              (App₁ {τ₇ = τ₈} {τ₈ = τ₉} {τ₉ = .τ₇} {τ₃ = .τ₃} {τ₃' = .τ₂} {τ₄ = .τ₄}
                    {τ₄' = .τ₄} {τ₅ = .τ₅} {τ₅' = .τ₅} e₂) {p₁ = p₁} {p₂ = p₂} same-con) sche =
  begin
    cpsI τ₄ τ₅ τ₃
         (pcontext-plug (Frame (App₁ e₂) p₁) (NonVal (App (Val Shift) (Val v)))) κ
  ≡⟨ refl ⟩
    cpsI τ₄ τ₅ τ₃
         (pframe-plug (App₁ e₂) (pcontext-plug p₁ (NonVal (App (Val Shift) (Val v))))) κ
  ≡⟨ refl ⟩
    cpsI τ₄ τ₅ τ₃
         (NonVal (App (pcontext-plug p₁ (NonVal (App (Val Shift) (Val v)))) e₂)) κ
  ≡⟨ refl ⟩
    cpsI (τ₈ ⇒ τ₄ cps[ τ₅ , τ₉ ]) τ₇ τ₃ (pcontext-plug p₁ (NonVal (App (Val Shift) (Val v))))
         (λ m → cpsI τ₈ τ₉ τ₇ e₂
         (λ n → CPSApp (CPSApp (CPSVal m) (CPSVal n)) (CPSVal (CPSFun (λ a → κ (CPSVar a))))))
  ≡⟨ contextContE v (λ m → cpsI τ₈ τ₉ τ₇ e₂
                    (λ n → CPSApp (CPSApp (CPSVal m) (CPSVal n)) (CPSVal (CPSFun (λ a → κ (CPSVar a))))))
                  p₁ p₂ same-con
                  (λ v₁ → κSubst e₂
                           (λ m n → CPSApp (CPSApp (CPSVal m) (CPSVal n))
                                            (CPSVal (CPSFun λ a → κ (CPSVar a))))
                            λ x → sApp (sApp (sVal sVar=) Subst≠) Subst≠) ⟩
    cpsI′ τ₁ τ₂ τ₃ (NonVal (App (Val Shift) (Val v)))
          (CPSFun (λ a′ → cpsI (τ₈ ⇒ τ₄ cps[ τ₅ , τ₉ ]) τ₇ τ₂ (pcontext-plug p₂ (Val (Var a′)))
                  (λ m → cpsI τ₈ τ₉ τ₇ e₂
                  (λ n → CPSApp (CPSApp (CPSVal m) (CPSVal n)) (CPSVal (CPSFun (λ a → κ (CPSVar a))))))))
  ≡⟨ refl ⟩
     cpsI′ τ₁ τ₂ τ₃ (NonVal (App (Val Shift) (Val v)))
           (CPSFun (λ a → cpsI τ₄ τ₅ τ₂
                   (NonVal (App (pcontext-plug p₂ (Val (Var a))) e₂)) κ))
  ≡⟨ refl ⟩
    cpsI′ τ₁ τ₂ τ₃ (NonVal (App (Val Shift) (Val v)))
          (CPSFun (λ a → cpsI τ₄ τ₅ τ₂ (pcontext-plug (Frame (App₁ e₂) p₂) (Val (Var a))) κ))
  ∎
   where open ≡-Reasoning

contextContE {var} {τ₁} {τ₂} {τ₃} {τ₄} {τ₅} {α} {β} {γ} v κ
             .(Frame {_} {τ₁} {τ₂} {τ₃} {τ₆} {τ₇} {τ₃} {τ₄} {τ₅} {τ₃}
                     (App₂ {_} {τ₄} {τ₆} {τ₅} {τ₇} {τ₃} v₁) p₁)
             .(Frame {_} {τ₁} {γ} {γ} {τ₆} {τ₇} {τ₂} {τ₄} {τ₅} {τ₂}
                     (App₂ {_} {τ₄} {τ₆} {τ₅} {τ₇} {τ₂} v₁) p₂)
             (Frame {τ₁ = .τ₁} {τ₁' = .τ₁} {τ₂ = .τ₂} {τ₂' = .γ} {τ₃ = .τ₃}
                    {τ₃' = .γ} {τ₄ = τ₆} {τ₄' = .τ₆} {τ₅ = τ₇} {τ₅' = .τ₇}
                    {τ₆ = .τ₃} {τ₆' = .τ₂} {τ₇ = .τ₄} {τ₇' = .τ₄} {τ₈ = .τ₅}
                    {τ₈' = .τ₅} {τ₉ = .τ₃} {τ₉' = .τ₂}
                    {f₁ = .(App₂ {_} {τ₄} {τ₆} {τ₅} {τ₇} {τ₃} v₁)}
                    {f₂ = .(App₂ {_} {τ₄} {τ₆} {τ₅} {τ₇} {τ₂} v₁)}
             (App₂ {τ₇ = .τ₄} {τ₈ = .τ₆} {τ₉ = .τ₅} {τ₁₀ = .τ₇} {τ₃ = .τ₃} {τ₃' = .τ₂} v₁)
             {p₁ = p₁} {p₂ = p₂} same-con) sche = 
  begin
    cpsI τ₄ τ₅ τ₃
      (pcontext-plug (Frame (App₂ v₁) p₁) (NonVal (App (Val Shift) (Val v)))) κ
  ≡⟨ refl ⟩
    cpsI τ₄ τ₅ τ₃
      (pframe-plug (App₂ v₁) (pcontext-plug p₁ (NonVal (App (Val Shift) (Val v))))) κ
  ≡⟨ refl ⟩
    cpsI τ₄ τ₅ τ₃
      (NonVal (App (Val v₁) (pcontext-plug p₁ (NonVal (App (Val Shift) (Val v)))))) κ
  ≡⟨ refl ⟩
    cpsI (τ₆ ⇒ τ₄ cps[ τ₅ , τ₇ ]) τ₃ τ₃ (Val v₁)
         (λ m → cpsI τ₆ τ₇ τ₃ (pcontext-plug p₁ (NonVal (App (Val Shift) (Val v))))
         (λ n → CPSApp (CPSApp (CPSVal m) (CPSVal n)) (CPSVal (CPSFun (λ a → κ (CPSVar a))))))
  ≡⟨ refl ⟩
    cpsI τ₆ τ₇ τ₃ (pcontext-plug p₁ (NonVal (App (Val Shift) (Val v))))
         (λ n → CPSApp (CPSApp (CPSVal (cpsV (τ₆ ⇒ τ₄ cps[ τ₅ , τ₇ ]) v₁)) (CPSVal n)) (CPSVal (CPSFun (λ a → κ (CPSVar a)))))
  ≡⟨ contextContE v
         (λ n → CPSApp (CPSApp (CPSVal (cpsV (τ₆ ⇒ τ₄ cps[ τ₅ , τ₇ ]) v₁)) (CPSVal n)) (CPSVal (CPSFun (λ a → κ (CPSVar a)))))
         p₁ p₂ same-con
         (λ v₂ → sApp (sApp Subst≠ (sVal sVar=)) Subst≠) ⟩
    cpsI′ τ₁ τ₂ τ₃ (NonVal (App (Val Shift) (Val v)))
          (CPSFun (λ a → cpsI τ₆ τ₇ τ₂ (pcontext-plug p₂ (Val (Var a)))
                  λ n →
                    CPSApp
                      (CPSApp (CPSVal (cpsV (τ₆ ⇒ τ₄ cps[ τ₅ , τ₇ ]) v₁)) (CPSVal n))
                      (CPSVal (CPSFun (λ a → κ (CPSVar a))))))
  ≡⟨ refl ⟩
    cpsI′ τ₁ τ₂ τ₃ (NonVal (App (Val Shift) (Val v)))
          (CPSFun (λ a → cpsI (τ₆ ⇒ τ₄ cps[ τ₅ , τ₇ ]) τ₂ τ₂ (Val v₁)
            (λ m → cpsI τ₆ τ₇ τ₂ (pcontext-plug p₂ (Val (Var a)))
            (λ n → CPSApp (CPSApp (CPSVal m) (CPSVal n)) (CPSVal (CPSFun (λ a → κ (CPSVar a))))))))
  ≡⟨ refl ⟩
    cpsI′ τ₁ τ₂ τ₃ (NonVal (App (Val Shift) (Val v)))
          (CPSFun (λ a →
            cpsI τ₄ τ₅ τ₂ (NonVal (App (Val v₁) (pcontext-plug p₂ (Val (Var a))))) κ))
  ≡⟨ refl ⟩
    cpsI′ τ₁ τ₂ τ₃ (NonVal (App (Val Shift) (Val v)))
          (CPSFun (λ a → cpsI τ₄ τ₅ τ₂ (pcontext-plug (Frame (App₂ v₁) p₂) (Val (Var a))) κ))
  ∎
  where open ≡-Reasoning

contextContE {var} {τ₁} {τ₂} {τ₃} {τ₄} {τ₅} {α} {β} {γ} v κ
             .(Frame {_} {τ₁} {τ₂} {τ₃} {τ₆} {τ₇} {τ₃} {τ₄} {τ₅} {τ₃}
                     (Let {_} {τ₆} {τ₄} {τ₅} {τ₇} {τ₃} e₂) p₁)
             .(Frame {_} {τ₁} {γ} {γ} {τ₆} {τ₇} {τ₂} {τ₄} {τ₅} {τ₂}
                     (Let {_} {τ₆} {τ₄} {τ₅} {τ₇} {τ₂} e₂) p₂)
             (Frame {τ₁ = .τ₁} {τ₁' = .τ₁} {τ₂ = .τ₂} {τ₂' = .γ} {τ₃ = .τ₃} {τ₃' = .γ}
                    {τ₄ = τ₆} {τ₄' = .τ₆} {τ₅ = τ₇} {τ₅' = .τ₇} {τ₆ = .τ₃} {τ₆' = .τ₂}
                    {τ₇ = .τ₄} {τ₇' = .τ₄} {τ₈ = .τ₅} {τ₈' = .τ₅} {τ₉ = .τ₃} {τ₉' = .τ₂}
                    {f₁ = .(Let {_} {τ₆} {τ₄} {τ₅} {τ₇} {τ₃} e₂)}
                    {f₂ = .(Let {_} {τ₆} {τ₄} {τ₅} {τ₇} {τ₂} e₂)}
             (Let {τ₇ = .τ₄} {τ₈ = .τ₆} {τ₉ = .τ₅} {τ₁₀ = .τ₇} {τ₃ = .τ₃} {τ₃' = .τ₂} e₂)
             {p₁ = p₁} {p₂ = p₂} same-con) sche =
  begin
    cpsI τ₄ τ₅ τ₃
      (pcontext-plug (Frame (Let e₂) p₁) (NonVal (App (Val Shift) (Val v)))) κ
  ≡⟨ refl ⟩
    cpsI τ₄ τ₅ τ₃
      (pframe-plug (Let e₂) (pcontext-plug p₁ (NonVal (App (Val Shift) (Val v))))) κ
  ≡⟨ refl ⟩
    cpsI τ₄ τ₅ τ₃
         (NonVal (Let (pcontext-plug p₁ (NonVal (App (Val Shift) (Val v)))) e₂)) κ
  ≡⟨ refl ⟩
    cpsI τ₆ τ₇ τ₃ (pcontext-plug p₁ (NonVal (App (Val Shift) (Val v))))
         (λ m → CPSLet (CPSVal m) (λ x → cpsI τ₄ τ₅ τ₇ (e₂ x) κ))
  ≡⟨ contextContE v
        (λ m → CPSLet (CPSVal m) (λ x → cpsI τ₄ τ₅ τ₇ (e₂ x) κ))
        p₁ p₂ same-con
        (λ v₁ → sLet (λ x → Subst≠) (λ x → sVal sVar=)) ⟩
    cpsI′ τ₁ τ₂ τ₃ (NonVal (App (Val Shift) (Val v)))
          (CPSFun (λ a → cpsI τ₄ τ₅ τ₂
                               (NonVal (Let (pcontext-plug p₂ (Val (Var a))) e₂)) κ))
  ≡⟨ refl ⟩
    cpsI′ τ₁ τ₂ τ₃ (NonVal (App (Val Shift) (Val v)))
          (CPSFun (λ a → cpsI τ₄ τ₅ τ₂ (pcontext-plug (Frame (Let e₂) p₂) (Val (Var a))) κ))
  ∎
  where open ≡-Reasoning

