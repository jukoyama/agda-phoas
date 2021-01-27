module CPSprove where

open import DSterm
open import CPSterm
open import reasoning
open import lemma1
open import lemma2
open import lemma3
open import lemma4

open import Function
open import Relation.Binary.PropositionalEquality

{----------------Term Definition----------------}

correctEta : {var : cpstyp → Set} → {τ₁ τ₂ τ₃ : typ} →
             {e  : term[ var ∘ cpsT ] τ₁ cps[ τ₂ , τ₃ ]} →
             {e′ : term[ var ∘ cpsT ] τ₁ cps[ τ₂ , τ₃ ]} →
             (κ : cpsvalue[ var ] (cpsT τ₁) → cpsterm[ var ] (cpsT τ₂)) →
             schematic κ →
             Reduce e e′ →
             cpsequal (cpsI τ₁ τ₂ τ₃ e κ) (cpsI τ₁ τ₂ τ₃ e′ κ)

correctEta {var} {τ₁} {τ₂} {τ₃}
           {.(NonVal {_} {τ₁} {τ₂} {τ₃}
                     (App {_} {τ₁} {τ} {τ₂} {τ₃} {τ₃} {τ₃}
                          (Val {_} {τ ⇒ τ₁ cps[ τ₂ , τ₃ ]} {τ₃} (Fun τ₁ τ {τ₂} {τ₃} e₁))
                          (Val {_} {τ} {τ₃} v₂)))}
           {e₂} κ sche
           (RBeta {τ = τ} {τ₁ = .τ₁} {τ₂ = .τ₂} {τ₃ = .τ₃} {e₁ = e₁} {v₂ = v₂} {e₁′ = e₂} sub) =
  begin
    cpsI τ₁ τ₂ τ₃ (NonVal (App (Val (Fun τ₁ τ e₁)) (Val v₂))) κ
  ≡⟨ refl ⟩
    cpsI (τ ⇒ τ₁ cps[ τ₂ , τ₃ ]) τ₃ τ₃ (Val (Fun τ₁ τ e₁))
         (λ m → cpsI τ τ₃ τ₃ (Val v₂)
         (λ n → CPSApp (CPSApp (CPSVal m) (CPSVal n))
                        (CPSVal (CPSFun (λ a → κ (CPSVar a))))))
  ≡⟨ refl ⟩
    cpsI τ τ₃ τ₃ (Val v₂)
         (λ n → CPSApp
                    (CPSApp (CPSVal (CPSFun (λ x → CPSVal (CPSFun (λ k →
                               cpsI′ τ₁ τ₂ τ₃ (e₁ x) (CPSVar k)))))) (CPSVal n))
                    (CPSVal (CPSFun (λ a → κ (CPSVar a)))))
  ≡⟨ refl ⟩
    CPSApp (CPSApp (CPSVal (CPSFun (λ x → CPSVal (CPSFun (λ k →
                       cpsI′ τ₁ τ₂ τ₃ (e₁ x) (CPSVar k))))))
                   (CPSVal (cpsV τ v₂)))
           (CPSVal (CPSFun (λ a → κ (CPSVar a))))
  ⟶⟨ eqApp₁ (eqBeta (sVal (sFun (λ k → ekSubst′ k sub)))) ⟩
    CPSApp (CPSVal (CPSFun (λ k → cpsI′ τ₁ τ₂ τ₃ e₂ (CPSVar k))))
           (CPSVal (CPSFun (λ a → κ (CPSVar a))))
  ⟶⟨ eqBeta (kSubst′ e₂ sVar=) ⟩
    cpsI′ τ₁ τ₂ τ₃ e₂ (CPSFun (λ a → κ (CPSVar a)))
  ⟶⟨ cpsEtaEta′ e₂ κ sche ⟩
    cpsI τ₁ τ₂ τ₃ e₂ κ
  ∎
           
correctEta {var} {τ₁} {τ₂} {τ₃}
           {.(NonVal {_} {τ₁} {τ₂} {τ₃}
             (App {_} {τ₁} {τ₄} {τ₂} {τ₆} {τ₅} {τ₃} e₁ e₂))}
           {.(NonVal {_} {τ₁} {τ₂} {τ₃}
             (App {_} {τ₁} {τ₄} {τ₂} {τ₆} {τ₅} {τ₃} e₁′ e₂))} κ sche
           (RFrame {τ₁ = .(τ₄ ⇒ τ₁ cps[ τ₂ , τ₆ ])} {τ₂ = τ₅} {τ₃ = .τ₃}
                   {τ₄ = .τ₁} {τ₅ = .τ₂} {τ₆ = .τ₃} {e₁ = e₁} {e₂ = e₁′}
                   (App₁ {τ₁ = .τ₁} {τ₂ = τ₄} {τ₃ = .τ₂} {τ₄ = τ₆} {τ₅ = .τ₅} {τ₆ = .τ₃} e₂) red) =
  begin
    cpsI τ₁ τ₂ τ₃ (frame-plug (App₁ e₂) e₁) κ
  ≡⟨ refl ⟩
    cpsI τ₁ τ₂ τ₃ (NonVal (App e₁ e₂)) κ
  ≡⟨ refl ⟩
    cpsI (τ₄ ⇒ τ₁ cps[ τ₂ , τ₆ ]) τ₅ τ₃ e₁
         (λ m → cpsI τ₄ τ₆ τ₅ e₂
         (λ n → CPSApp (CPSApp (CPSVal m) (CPSVal n)) (CPSVal (CPSFun (λ a → κ (CPSVar a))))))
  ⟶⟨ correctEta
        (λ m → cpsI τ₄ τ₆ τ₅ e₂
             　　(λ n → CPSApp (CPSApp (CPSVal m) (CPSVal n)) (CPSVal (CPSFun (λ a → κ (CPSVar a))))))
        (λ v₁ v₁′ v sub →
        κSubst e₂
               (λ v′ n → CPSApp (CPSApp (CPSVal v′) (CPSVal n)) (CPSVal (CPSFun (λ a → κ (CPSVar a)))))
               (λ x₁ sub₁ → sApp (sApp (sVal sub₁) Subst≠) Subst≠) sub)
        red ⟩
    cpsI (τ₄ ⇒ τ₁ cps[ τ₂ , τ₆ ]) τ₅ τ₃ e₁′
         (λ m → cpsI τ₄ τ₆ τ₅ e₂
         (λ n → CPSApp (CPSApp (CPSVal m) (CPSVal n))
                        (CPSVal (CPSFun (λ a → κ (CPSVar a))))))
  ≡⟨ refl ⟩
    cpsI τ₁ τ₂ τ₃ (frame-plug (App₁ e₂) e₁′) κ
  ∎

correctEta {var} {τ₁} {τ₂} {τ₃}
           {.(NonVal {_} {τ₁} {τ₂} {τ₃}
             (App {_} {τ₁} {τ₄} {τ₂} {τ₅} {τ₃} {τ₃}
                  (Val {_} {τ₄ ⇒ τ₁ cps[ τ₂ , τ₅ ]} {τ₃} v₁) e₂))}
           {.(NonVal {_} {τ₁} {τ₂} {τ₃}
             (App {_} {τ₁} {τ₄} {τ₂} {τ₅} {τ₃} {τ₃}
                  (Val {_} {τ₄ ⇒ τ₁ cps[ τ₂ , τ₅ ]} {τ₃} v₁) e₂′))} κ sche
           (RFrame {τ₁ = τ₄} {τ₂ = τ₅} {τ₃ = .τ₃} {τ₄ = .τ₁} {τ₅ = .τ₂} {τ₆ = .τ₃} {e₁ = e₂} {e₂ = e₂′}
             (App₂ {τ₁ = .τ₁} {τ₂ = .τ₄} {τ₃ = .τ₂} {τ₄ = .τ₅} {τ₅ = .τ₃} v₁) red) =
  begin
    cpsI τ₁ τ₂ τ₃ (frame-plug (App₂ v₁) e₂) κ
  ≡⟨ refl ⟩
    cpsI τ₄ τ₅ τ₃ e₂
         (λ n → CPSApp
                    (CPSApp (CPSVal (cpsV (τ₄ ⇒ τ₁ cps[ τ₂ , τ₅ ]) v₁)) (CPSVal n))
                    (CPSVal (CPSFun (λ a → κ (CPSVar a)))))
  ⟶⟨ correctEta
        (λ n →
          CPSApp
            (CPSApp (CPSVal (cpsV (τ₄ ⇒ τ₁ cps[ τ₂ , τ₅ ]) v₁)) (CPSVal n))
            (CPSVal (CPSFun (λ a → κ (CPSVar a)))))
        (λ v₂ v₁′ v sub → sApp (sApp Subst≠ (sVal sub)) Subst≠)
        red ⟩
    cpsI τ₄ τ₅ τ₃ e₂′
         (λ n → CPSApp
                    (CPSApp (CPSVal (cpsV (τ₄ ⇒ τ₁ cps[ τ₂ , τ₅ ]) v₁)) (CPSVal n))
                    (CPSVal (CPSFun (λ a → κ (CPSVar a)))))
  ≡⟨ refl ⟩
    cpsI τ₁ τ₂ τ₃ (frame-plug (App₂ v₁) e₂′) κ
  ∎


correctEta {var} {τ₁} {τ₂} {.τ₂}
           {.(NonVal {_} {τ₁} {τ₂} {τ₂} (Reset τ₄ τ₁ τ₂ e))}
           {.(NonVal {_} {τ₁} {τ₂} {τ₂} (Reset τ₄ τ₁ τ₂ e′))} κ sche
           (RFrame {τ₁ = τ₄} {τ₂ = .τ₄} {τ₃ = .τ₁} {τ₄ = .τ₁} {τ₅ = .τ₂} {τ₆ = .τ₂} {e₁ = e} {e₂ = e′}
           (Reset {τ₁ = .τ₄} {τ₂ = .τ₁} {τ₃ = .τ₂}) red) =
  begin
    cpsI τ₁ τ₂ τ₂ (frame-plug Reset e) κ
  ≡⟨ refl ⟩
    CPSApp (CPSVal (CPSFun (λ x → κ (CPSVar x))))
           (cpsI τ₄ τ₄ τ₁ e (λ m → CPSVal m))
  ⟶⟨ eqApp₂ (correctEta (λ m → CPSVal m) (λ v₁ v₁′ v x → sVal x) red) ⟩
    CPSApp (CPSVal (CPSFun (λ x → κ (CPSVar x))))
           (cpsI τ₄ τ₄ τ₁ e′ (λ m → CPSVal m))
  ≡⟨ refl ⟩
    cpsI τ₁ τ₂ τ₂ (frame-plug Reset e′) κ
  ∎


correctEta {var} {τ₁} {τ₂} {τ₃}
           {.(NonVal {_} {τ₁} {τ₂} {τ₃} (Let {_} {τ₄} {τ₁} {τ₂} {τ₅} {τ₃} e₁  e₂))}
           {.(NonVal {_} {τ₁} {τ₂} {τ₃} (Let {_} {τ₄} {τ₁} {τ₂} {τ₅} {τ₃} e₁′ e₂))} κ sche
             (RFrame {τ₁ = τ₄} {τ₂ = τ₅} {τ₃ = .τ₃} {τ₄ = .τ₁} {τ₅ = .τ₂} {τ₆ = .τ₃}
                     {e₁ = e₁} {e₂ = e₁′}
           (Let {τ₁ = .τ₄} {τ₂ = .τ₁} {α = .τ₂} {β = .τ₅} {γ = .τ₃} e₂) red) =
  begin
    cpsI τ₁ τ₂ τ₃ (frame-plug (Let e₂) e₁) κ
  ≡⟨ refl ⟩
    cpsI τ₄ τ₅ τ₃ e₁
         (λ m →
              CPSApp (CPSVal (CPSFun (λ c → cpsI τ₁ τ₂ τ₅ (e₂ c) κ))) (CPSVal m))
  ⟶⟨ correctEta
        (λ m → CPSApp (CPSVal (CPSFun (λ c → cpsI τ₁ τ₂ τ₅ (e₂ c) κ))) (CPSVal m))
        (λ v₁ v₁′ v sub → sApp Subst≠ (sVal sub))
        red ⟩
    cpsI τ₄ τ₅ τ₃ e₁′
         (λ m → CPSApp (CPSVal (CPSFun (λ c → cpsI τ₁ τ₂ τ₅ (e₂ c) κ))) (CPSVal m))
  ≡⟨ refl ⟩
    cpsI τ₁ τ₂ τ₃ (frame-plug (Let e₂) e₁′) κ
  ∎

correctEta {var} {τ₁} {τ₂} {τ₃}
           {.(NonVal {_} {τ₁} {τ₂} {τ₃}
             (Let {_} {τ₄} {τ₁} {τ₂} {τ₃} {τ₃}
                  (Val {_} {τ₄} {τ₃} v₁) e₂))}
           {e′} κ sche
           (RLet {τ₁ = τ₄} {τ₂ = .τ₁} {α = .τ₂} {β = .τ₃} {v₁ = v₁} {e₂ = e₂} {e₂′ = .e′} sub) =
  begin
    cpsI τ₁ τ₂ τ₃ (NonVal (Let (Val v₁) e₂)) κ
  ≡⟨ refl ⟩
    CPSApp (CPSVal (CPSFun (λ c → cpsI τ₁ τ₂ τ₃ (e₂ c) κ)))
           (CPSVal (cpsV τ₄ v₁))
  ⟶⟨ eqBeta (eSubst {e₁ = λ c → e₂ c} {e₂ = e′} {v = v₁} {κ = κ} sub sche) ⟩
    cpsI τ₁ τ₂ τ₃ e′ κ
  ∎


correctEta {var} {τ₁} {τ₂} {.τ₂}
           {.(NonVal {_} {τ₁} {τ₂} {τ₂}
             (Reset τ₁ τ₁ τ₂ (Val {_} {τ₁} {τ₁} v₁)))}
           {.(Val {_} {τ₁} {τ₂} v₁)} κ sche
           (RReset {τ₁ = .τ₁} {τ₂ = .τ₂} {v₁ = v₁}) =
  begin
    cpsI τ₁ τ₂ τ₂ (NonVal (Reset τ₁ τ₁ τ₂ (Val v₁))) κ
  ≡⟨ refl ⟩
    CPSApp (CPSVal (CPSFun (λ x → κ (CPSVar x)))) (CPSVal (cpsV τ₁ v₁))
  ⟶⟨ eqBeta (sche (λ z → CPSVar z) (cpsV τ₁ v₁) (cpsV τ₁ v₁) (eSubstV sVar=)) ⟩
    cpsI τ₁ τ₂ τ₂ (Val v₁) κ
  ∎

correctEta {var} {τ₁} {τ₂} {.τ₂}
           {.(NonVal {_} {τ₁} {τ₂} {τ₂}
             (Reset τ₆ τ₁ τ₂ (pcontext-plug {λ x₁ → var (cpsT x₁)}
                    {τ₄} {τ₅} {τ₁} {τ₆} {τ₆} {τ₁} p₁
             (NonVal {_} {τ₄} {τ₅} {τ₁}
               (App {_} {τ₄} {(τ₄ ⇒ τ₅ cps[ τ , τ ]) ⇒ τ₃ cps[ τ₃ , τ₁ ]} {τ₅} {τ₁} {τ₁} {τ₁}
                    (Val {_} {((τ₄ ⇒ τ₅ cps[ τ , τ ]) ⇒ τ₃ cps[ τ₃ , τ₁ ]) ⇒ τ₄ cps[ τ₅ , τ₁ ]} {τ₁}
                    (Shift {_} {τ} {τ₃} {τ₁} {τ₄} {τ₅}))
               (Val {_} {(τ₄ ⇒ τ₅ cps[ τ , τ ]) ⇒ τ₃ cps[ τ₃ , τ₁ ]} {τ₁} v₂))))))}
           {.(NonVal {_} {τ₁} {τ₂} {τ₂}
             (Reset τ₃ τ₁ τ₂
               (NonVal {_} {τ₃} {τ₃} {τ₁}
               (App {_} {τ₃} {τ₄ ⇒ τ₅ cps[ τ , τ ]} {τ₃} {τ₁} {τ₁} {τ₁}
                    (Val {_} {(τ₄ ⇒ τ₅ cps[ τ , τ ]) ⇒ τ₃ cps[ τ₃ , τ₁ ]} {τ₁} v₂)
                    (Val {_} {τ₄ ⇒ τ₅ cps[ τ , τ ]} {τ₁} (Fun τ₅ τ₄ {τ} {τ}
                         (λ x₁ → NonVal {_} {τ₅} {τ} {τ}
                         (Reset τ₆ τ₅ τ (pcontext-plug {λ x₂ → var (cpsT x₂)} {τ₄} {τ₅} {τ₅} {τ₆} {τ₆} {τ₅}
                                p₂ (Val {_} {τ₄} {τ₅} (Var {_} {τ₄} x₁)))))))))))}
          κ sche (RShift {τ = τ} {τ₁ = τ₃} {τ₂ = .τ₁} {τ₃ = τ₄} {τ₄ = τ₅} {τ₅ = τ₆} {τ₆ = .τ₂} {v₂ = v₂} p₁ p₂ same-con) =
  begin
    cpsI τ₁ τ₂ τ₂
         (NonVal (Reset τ₆ τ₁ τ₂ (pcontext-plug p₁ (NonVal (App (Val Shift) (Val v₂))))))
         κ
  ≡⟨ refl ⟩
    CPSApp (CPSVal (CPSFun (λ x → κ (CPSVar x))))
           (cpsI τ₆ τ₆ τ₁ (pcontext-plug p₁ (NonVal (App (Val Shift) (Val v₂)))) (λ m → CPSVal m))
  ≡⟨ cong₂ CPSApp refl
      (contextContE v₂ (λ m → CPSVal m) p₁ p₂ same-con λ v₁ v₁′ v x → sVal x) ⟩
    CPSApp (CPSVal (CPSFun (λ x → κ (CPSVar x))))
           (cpsI′ τ₄ τ₅ τ₁ (NonVal (App (Val Shift) (Val v₂)))
                  (CPSFun (λ a → cpsI τ₆ τ₆ τ₅ (pcontext-plug p₂ (Val (Var a))) (λ m → CPSVal m))))
  ≡⟨ refl ⟩
    CPSApp
      (CPSVal (CPSFun (λ x → κ (CPSVar x))))
      (CPSApp (CPSApp (CPSVal (CPSFun (λ w → CPSVal (CPSFun (λ k →
                               CPSApp (CPSApp (CPSVal (CPSVar w))
                                              (CPSVal (CPSFun (λ a → CPSVal (CPSFun (λ k′ →
                                                       CPSApp (CPSVal (CPSVar k′))
                                                              (CPSApp (CPSVal (CPSVar k)) (CPSVal (CPSVar a)))))))))
                                      (CPSVal (CPSFun (λ m → CPSVal (CPSVar m)))))))))
                      (CPSVal (cpsV ((τ₄ ⇒ τ₅ cps[ τ , τ ]) ⇒ τ₃ cps[ τ₃ , τ₁ ]) v₂)))
              (CPSVal (CPSFun (λ a → cpsI τ₆ τ₆ τ₅ (pcontext-plug p₂ (Val (Var a))) (λ m → CPSVal m)))))
  ⟶⟨ eqApp₂ eqShift ⟩
    CPSApp
      (CPSVal (CPSFun (λ x → κ (CPSVar x))))
      (CPSApp (CPSApp (CPSVal (cpsV ((τ₄ ⇒ τ₅ cps[ τ , τ ]) ⇒ τ₃ cps[ τ₃ , τ₁ ]) v₂))
                      (CPSVal (CPSFun (λ a → CPSVal (CPSFun (λ k′ →
                               CPSApp (CPSVal (CPSVar k′))
                                      (CPSApp (CPSVal (CPSFun (λ a₁ →
                                                       cpsI τ₆ τ₆ τ₅ (pcontext-plug p₂ (Val (Var a₁))) (λ m → CPSVal m))))
                                              (CPSVal (CPSVar a)))))))))
              (CPSVal (CPSFun (λ m → CPSVal (CPSVar m)))))
  ⟶⟨ eqApp₂ (eqApp₁ (eqApp₂ (eqFun (λ a → eqFun (λ k′ → eqApp₂ (eqBeta
             (eSubst {e₁ = λ a₁ → (pcontext-plug p₂ (Val (Var a₁)))}
                     {e₂ = pcontext-plug p₂ (Val (Var a))}
                     (subst-context p₂ (Var a))
                     λ v₁ v₁′ v x → sVal x))))))) ⟩
    CPSApp
      (CPSVal (CPSFun (λ x → κ (CPSVar x))))
      (CPSApp (CPSApp (CPSVal (cpsV ((τ₄ ⇒ τ₅ cps[ τ , τ ]) ⇒ τ₃ cps[ τ₃ , τ₁ ]) v₂))
                      (CPSVal (CPSFun (λ a → CPSVal (CPSFun (λ k′ →
                               CPSApp (CPSVal (CPSVar k′))
                                      (cpsI τ₆ τ₆ τ₅ (pcontext-plug p₂ (Val (Var a))) (λ m → CPSVal m))))))))
              (CPSVal (CPSFun (λ m → CPSVal (CPSVar m)))))
  ≡⟨ refl ⟩
    CPSApp
      (CPSVal (CPSFun (λ x → κ (CPSVar x))))
      (CPSApp (CPSApp (CPSVal (cpsV ((τ₄ ⇒ τ₅ cps[ τ , τ ]) ⇒ τ₃ cps[ τ₃ , τ₁ ]) v₂))
                      (CPSVal (CPSFun (λ a → CPSVal (CPSFun λ k′ →
                              cpsI′ τ₅ τ τ
                                    (NonVal (Reset τ₆ τ₅ τ (pcontext-plug p₂ (Val (Var a)))))
                                    (CPSVar k′))))))
              (CPSVal (CPSFun (λ m → CPSVal (CPSVar m)))))
  ≡⟨ refl ⟩
    CPSApp
      (CPSVal (CPSFun (λ x → κ (CPSVar x))))
      (CPSApp (CPSApp (CPSVal (cpsV ((τ₄ ⇒ τ₅ cps[ τ , τ ]) ⇒ τ₃ cps[ τ₃ , τ₁ ]) v₂))
                      (CPSVal (cpsV (τ₄ ⇒ τ₅ cps[ τ , τ ]) (Fun τ₅ τ₄ (λ a → NonVal
                                    (Reset τ₆ τ₅ τ (pcontext-plug p₂ (Val (Var a)))))))))
              (CPSVal (CPSFun (λ m → CPSVal (CPSVar m)))))
  ≡⟨ refl ⟩
    CPSApp
      (CPSVal (CPSFun (λ x → κ (CPSVar x))))
      (cpsI τ₃ τ₃ τ₁
            (NonVal (App (Val v₂)
                         (Val (Fun τ₅ τ₄ (λ a → NonVal
                              (Reset τ₆ τ₅ τ (pcontext-plug p₂ (Val (Var a)))))))))
            λ m → CPSVal m)
  ≡⟨ refl ⟩
    cpsI τ₁ τ₂ τ₂
         (NonVal (Reset τ₃ τ₁ τ₂
           (NonVal (App (Val v₂)
                        (Val (Fun τ₅ τ₄ (λ x → NonVal (Reset τ₆ τ₅ τ (pcontext-plug p₂ (Val (Var x)))))))))))
         κ
  ∎
