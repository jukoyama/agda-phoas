module CPSprove where

open import DSterm
open import CPSterm
open import lemma1
open import lemma2
open import lemma3

open import Function
open import Relation.Binary.PropositionalEquality

  -- cpsI′ : (τ₁ τ₂ τ₃ : typ) → {var : cpstyp → Set} →
  --         term[ var ∘ cpsT ] τ₁ cps[ τ₂ , τ₃ ] →
  --         cpsvalue[ var ] (cpsT τ₁ ⇒ cpsT τ₂) →
  --         cpsterm[ var ] (cpsT τ₃)

  -- cpsI′ τ₁ τ₂ .τ₂ (Reset τ₃ .τ₁ .τ₂ e₁) k =
  --   -- CPSApp (CPSVal k) (cpsI τ₃ τ₃ τ₁ e₁ (λ m → CPSVal m)) 
  --   CPSLet (cpsI τ₃ τ₃ τ₁ e₁ (λ m → CPSVal m)) (λ a → CPSApp (CPSVal k) (CPSVal (CPSVar a)))

cpsResetEqual : {var : cpstyp → Set} → {τ₁ τ₂ τ₃ : typ} →
                (e₁ : term[ var ∘ cpsT ] τ₃ cps[ τ₃ , τ₁ ]) →
                {k : cpsvalue[ var ] (cpsT τ₁ ⇒ cpsT τ₂)} →
                -- (κ : cpsvalue[ var ] (cpsT τ₃) → cpsterm[ var ] (cpsT τ₃)) →
                cpsequal
                  (CPSLet (cpsI τ₃ τ₃ τ₁ e₁ (λ m → CPSVal m))
                          λ c → CPSApp (CPSVal k) (CPSVal (CPSVar c)))
                  (CPSApp (CPSVal k) (cpsI τ₃ τ₃ τ₁ e₁ (λ m → CPSVal m)))

cpsResetEqual {var} {τ₁} {τ₂} {.τ₁} (Val {τ₁ = .τ₁} {τ₂ = .τ₁} x) {k} = eqLet (sApp Subst≠ (sVal sVar=))
cpsResetEqual {var} {τ₁} {τ₂} {τ₃} (App {τ₁ = .τ₃} {τ₂ = τ₄} {τ₃ = .τ₃} {τ₄ = τ₅} {τ₅ = τ₆} {τ₆ = .τ₁} e₁ e₂) {k} =
  begin
    CPSLet (cpsI τ₃ τ₃ τ₁ (App e₁ e₂) (λ m → CPSVal m))
           (λ c → CPSApp (CPSVal k) (CPSVal (CPSVar c)))
  ≡⟨ refl ⟩
    CPSLet (cpsI (τ₄ ⇒ τ₃ cps[ τ₃ , τ₅ ]) τ₆ τ₁ e₁
             (λ m → cpsI τ₄ τ₅ τ₆ e₂ (λ n →
                CPSApp (CPSApp (CPSVal m) (CPSVal n)) (CPSVal (CPSFun (λ a → CPSVal (CPSVar a)))))))
             (λ c → CPSApp (CPSVal k) (CPSVal (CPSVar c)))
  ⟶⟨ {!!} ⟩
    {!!}
  ⟶⟨ {!!} ⟩
    CPSApp (CPSVal k) (cpsI τ₃ τ₃ τ₁ (App e₁ e₂) (λ m → CPSVal m))
  ∎
cpsResetEqual {var} {τ₁} {τ₂} {.τ₁} (Reset τ₃ .τ₁ .τ₁ e₁) {k} = {!!}
cpsResetEqual {var} {τ₁} {τ₂} {τ₃} (Shift τ τ₄ .τ₁ .τ₃ .τ₃ x) {k} = {!!}


{----------------Term Definition----------------}

correctII : {var : cpstyp → Set} → {τ₁ τ₂ τ₃ : typ} →
            {e  : term[ var ∘ cpsT ] τ₁ cps[ τ₂ , τ₃ ]} →
            {e′ : term[ var ∘ cpsT ] τ₁ cps[ τ₂ , τ₃ ]} →
            (κ : cpsvalue[ var ] (cpsT τ₁) → cpsterm[ var ] (cpsT τ₂)) →
            schematicV {var} {τ₁} {τ₂} κ →
            Reduce e e′ →
            cpsequal (cpsI τ₁ τ₂ τ₃ e κ) (cpsI τ₁ τ₂ τ₃ e′ κ)

correctII {τ₁ = τ₁} {τ₂} {τ₃} {e′ = e₂} κ sche (RBeta {τ} {e₁ = e₁} {v₂} {e₁′ = e₂} sub) =
  begin
    cpsI τ₁ τ₂ τ₃ (App (Val (Fun τ₁ τ e₁)) (Val v₂)) κ
  ≡⟨ refl ⟩
    CPSApp (CPSApp (CPSVal (CPSFun (λ x → CPSVal (CPSFun λ k → cpsI′ τ₁ τ₂ τ₃ (e₁ x) (CPSVar k)))))
                   (CPSVal (cpsV τ v₂)))
           (CPSVal (CPSFun (λ a → κ (CPSVar a))))
  ⟶⟨ eqApp₁ (eqBeta (sVal (sFun (λ k → ekSubst′ k sub)))) ⟩ 
    CPSApp (CPSVal (CPSFun (λ k → cpsI′ τ₁ τ₂ τ₃ e₂ (CPSVar k))))
           (CPSVal (CPSFun (λ a → κ (CPSVar a))))
  ⟶⟨ eqBeta (kSubst′ e₂) ⟩
    cpsI′ τ₁ τ₂ τ₃ e₂ (CPSFun (λ a → κ (CPSVar a)))
  ⟶⟨ cpsEtaEta′ e₂ κ sche ⟩
    cpsI τ₁ τ₂ τ₃ e₂ κ
  ∎

correctII {τ₁ = τ₁} {τ₂} {τ₃} κ sche
          (RFrame {τ₁ = .(τ₅ ⇒ τ₁ cps[ τ₂ , τ₆ ])} {τ₂ = τ₄} {τ₃ = .τ₃} {τ₄ = .τ₁} {τ₅ = .τ₂} {τ₆ = .τ₃}
          {e₁ = e₁} {e₂ = e₁′}
          (App₁ {τ₁ = .τ₁} {τ₂ = τ₅} {τ₃ = .τ₂} {τ₄ = τ₆} {τ₅ = .τ₄} {τ₆ = .τ₃} e₂) sub) =
  begin
    cpsI τ₁ τ₂ τ₃ (App e₁ e₂) κ
  ≡⟨ refl ⟩
    cpsI (τ₅ ⇒ τ₁ cps[ τ₂ , τ₆ ]) τ₄ τ₃ e₁
         (λ m → cpsI τ₅ τ₆ τ₄ e₂
         (λ n → CPSApp (CPSApp (CPSVal m) (CPSVal n)) (CPSVal (CPSFun (λ a → κ (CPSVar a))))))
  ⟶⟨ correctII (λ m → cpsI τ₅ τ₆ τ₄ e₂
                        (λ n → CPSApp (CPSApp (CPSVal m) (CPSVal n))
                                      (CPSVal (CPSFun (λ a → κ (CPSVar a))))))
                 (λ v → κSubst e₂ (λ m →
                                   (λ n → CPSApp (CPSApp (CPSVal m) (CPSVal n))
                                                  (CPSVal (CPSFun (λ a → κ (CPSVar a))))))
                                   λ k₁ → sApp (sApp (sVal sVar=) (sVal SubstV≠))
                                                (sVal (sFun (λ k₂ → Subst≠))))
                 sub ⟩
    cpsI (τ₅ ⇒ τ₁ cps[ τ₂ , τ₆ ]) τ₄ τ₃ e₁′
         (λ m → cpsI τ₅ τ₆ τ₄ e₂
         (λ n → CPSApp (CPSApp (CPSVal m) (CPSVal n))
                        (CPSVal (CPSFun (λ a → κ (CPSVar a))))))
  ⟶⟨ eqId ⟩
    cpsI τ₁ τ₂ τ₃ (App e₁′ e₂) κ
  ∎

correctII {τ₁ = τ₁} {τ₂} {τ₃} κ sche
          (RFrame {τ₁ = τ₄} {τ₂ = τ₅} {τ₃ = .τ₃} {τ₄ = .τ₁} {τ₅ = .τ₂} {τ₆ = .τ₃} {e₁ = e₂} {e₂ = e₂′}
          (App₂ {τ₁ = .τ₁} {τ₂ = .τ₄} {τ₃ = .τ₂} {τ₄ = .τ₅} {τ₅ = .τ₃} v₁) sub) =
  begin
    cpsI τ₁ τ₂ τ₃ (App (Val v₁) e₂) κ
  ≡⟨ refl ⟩
    cpsI (τ₄ ⇒ τ₁ cps[ τ₂ , τ₅ ]) τ₃ τ₃ (Val v₁)
    (λ m → cpsI τ₄ τ₅ τ₃ e₂
           (λ n → CPSApp (CPSApp (CPSVal m) (CPSVal n)) (CPSVal (CPSFun (λ a → κ (CPSVar a))))))
  ≡⟨ refl ⟩
    cpsI τ₄ τ₅ τ₃ e₂
    (λ n → CPSApp (CPSApp (CPSVal (cpsV (τ₄ ⇒ τ₁ cps[ τ₂ , τ₅ ]) v₁)) (CPSVal n))
                           (CPSVal (CPSFun (λ a → κ (CPSVar a)))))
  ⟶⟨ correctII (λ n → CPSApp (CPSApp (CPSVal (cpsV (τ₄ ⇒ τ₁ cps[ τ₂ , τ₅ ]) v₁)) (CPSVal n))
                               (CPSVal (CPSFun (λ a → κ (CPSVar a)))))
                (λ v → sApp (sApp (sVal SubstV≠) (sVal sVar=))
                             (sVal (sFun (λ a → Subst≠))))
                sub ⟩
    cpsI τ₄ τ₅ τ₃ e₂′
      (λ n′ → CPSApp (CPSApp (CPSVal (cpsV (τ₄ ⇒ τ₁ cps[ τ₂ , τ₅ ]) v₁)) (CPSVal n′))
                     (CPSVal (CPSFun (λ a → κ (CPSVar a)))))
  ⟶⟨ eqId ⟩
    cpsI τ₁ τ₂ τ₃ (App (Val v₁) e₂′) κ
  ∎

correctII {τ₁ = τ₁} {τ₂} {.τ₂} κ sche
          (RFrame {τ₁ = τ₃} {τ₂ = .τ₃} {τ₃ = .τ₁} {τ₄ = .τ₁} {τ₅ = .τ₂} {τ₆ = .τ₂} {e₁ = e} {e₂ = e′}
          (Reset {τ₁ = .τ₃} {τ₂ = .τ₁} {τ₃ = .τ₂}) sub) =
  begin
    cpsI τ₁ τ₂ τ₂ (Reset τ₃ τ₁ τ₂ e) κ
  ≡⟨ refl ⟩
    CPSLet (cpsI τ₃ τ₃ τ₁ e (λ m → CPSVal m))
           (λ c → κ (CPSVar c))
  ⟶⟨ eqLet₁ (λ c → κ (CPSVar c))
              (correctII (λ m → CPSVal m) (λ v → sVal sVar=) sub) ⟩
    CPSLet (cpsI τ₃ τ₃ τ₁ e′ CPSVal) (λ c → κ (CPSVar c))
  ⟶⟨ eqId ⟩
    cpsI τ₁ τ₂ τ₂ (Reset τ₃ τ₁ τ₂ e′) κ
  ∎

correctII {τ₁ = τ₁} {τ₂} {.τ₂} κ sche
          (RReset {τ₁ = .τ₁} {τ₂ = .τ₂} {v₁ = v}) =
  begin
    cpsI τ₁ τ₂ τ₂ (Reset τ₁ τ₁ τ₂ (Val v)) κ
  ≡⟨ refl ⟩
    CPSLet (cpsI τ₁ τ₁ τ₁ (Val v) (λ m → CPSVal m))
           (λ c → κ (CPSVar c))
  ≡⟨ refl ⟩
    CPSLet (CPSVal (cpsV τ₁ v)) (λ c → κ (CPSVar c))
  ⟶⟨ eqLet (sche v) ⟩
    κ (cpsV τ₁ v)
  ⟶⟨ eqId ⟩
    cpsI τ₁ τ₂ τ₂ (Val v) κ
  ∎

correctII {var} {τ₁} {τ₂} {.τ₂}
          {.(Reset τ₄ τ₁ τ₂ (pcontext-plug {λ x → var (cpsT x)} {τ₄} τ₀ {τ₄} {τ} {τ₁} p₁ (Shift α τ₃ τ₁ τ₀ τ e₁)))}
          {.(Reset τ₃ τ₁ τ₂ (App {_} {τ₃} {τ₀ ⇒ τ cps[ α , α ]} {τ₃} {τ₁} {τ₁} {τ₁}
                   (Val {_} {(τ₀ ⇒ τ cps[ α , α ]) ⇒ τ₃ cps[ τ₃ , τ₁ ]} {τ₁}
                        (Fun τ₃ (τ₀ ⇒ τ cps[ α , α ]) {τ₃} {τ₁} e₁))
                   (Val {_} {τ₀ ⇒ τ cps[ α , α ]} {τ₁}
                        (Fun τ τ₀ {α} {α}
                        (λ x → Reset τ₄ τ α (pcontext-plug {λ x₁ → var (cpsT x₁)} {τ₄} τ₀ {τ₄} {τ} {τ} p₂
                                                              (Val {_} {τ₀} {τ} (Var {_} {τ₀} x))))))))}
          κ sche
          (RShift {τ₀ = τ₀} {τ₁ = τ₃} {τ₂ = .τ₁} {τ₃ = .τ₂} {τ₄ = τ₄} {τ = τ} {α = α} p₁ p₂ same e₁) =
  begin
    cpsI τ₁ τ₂ τ₂
      (Reset τ₄ τ₁ τ₂ (pcontext-plug τ₀ p₁ (Shift α τ₃ τ₁ τ₀ τ e₁))) κ
  ≡⟨ refl ⟩
    CPSLet (cpsI τ₄ τ₄ τ₁
             (pcontext-plug τ₀ p₁ (Shift α τ₃ τ₁ τ₀ τ e₁))
             λ m → CPSVal m)
           (λ c → κ (CPSVar c))
  ⟶⟨ eqLet₁ (λ c → κ (CPSVar c)) (shift-lemma p₁ p₂ same e₁ (λ m → CPSVal m) (λ v → sVal sVar=)) ⟩
    CPSLet
      (cpsI τ₄ τ₄ τ₁ (App (Val (Fun τ₄ τ₀ (λ x → pcontext-plug τ₀ p₂ (Val (Var x))))) (Shift α τ₃ τ₁ τ₀ τ e₁))
                       (λ m → CPSVal m))
      (λ c → κ (CPSVar c))
  ≡⟨ refl ⟩
    CPSLet
      (cpsI (τ₀ ⇒ τ₄ cps[ τ₄ , τ ]) τ₁ τ₁
        (Val (Fun τ₄ τ₀ (λ x → pcontext-plug τ₀ p₂ (Val (Var x)))))
        (λ m → cpsI τ₀ τ τ₁
                  (Shift α τ₃ τ₁ τ₀ τ e₁)
                  (λ n → CPSApp (CPSApp (CPSVal m) (CPSVal n)) (CPSVal (CPSFun (λ a → (λ m → CPSVal m) (CPSVar a)))))))
      (λ c → κ (CPSVar c))
  ≡⟨ refl ⟩
    CPSLet
      ((λ m → cpsI τ₀ τ τ₁
                 (Shift α τ₃ τ₁ τ₀ τ e₁)
                 (λ n → CPSApp (CPSApp (CPSVal m) (CPSVal n)) (CPSVal (CPSFun (λ a → (λ m → CPSVal m) (CPSVar a))))))
       (CPSFun (λ x → CPSVal (CPSFun (λ k → cpsI′ τ₄ τ₄ τ
                                               (pcontext-plug τ₀ p₂ (Val (Var x))) (CPSVar k))))))
      (λ c → κ (CPSVar c))
  ≡⟨ refl ⟩
    CPSLet
      (cpsI τ₀ τ τ₁
        (Shift α τ₃ τ₁ τ₀ τ e₁)
        (λ n → CPSApp
                  (CPSApp (CPSVal (CPSFun (λ x → CPSVal (CPSFun (λ k →
                              cpsI′ τ₄ τ₄ τ (pcontext-plug τ₀ p₂ (Val (Var x))) (CPSVar k))))))
                          (CPSVal n))
                  (CPSVal (CPSFun (λ a → (λ  m → CPSVal m) (CPSVar a))))))
      (λ c → κ (CPSVar c))
  ≡⟨ refl ⟩
    CPSLet
      (CPSLet
        (CPSVal (CPSFun (λ a′ → CPSVal (CPSFun λ κ′ →
          CPSApp (CPSVal (CPSVar κ′))
                 (CPSApp
                   (CPSApp (CPSVal (CPSFun (λ x → CPSVal (CPSFun λ k →
                               cpsI′ τ₄ τ₄ τ (pcontext-plug τ₀ p₂ (Val (Var x))) (CPSVar k)))))
                           (CPSVal (CPSVar a′)))
                   (CPSVal (CPSFun (λ a → (λ m → CPSVal m) (CPSVar a)))))))))
        λ c′ → cpsI τ₃ τ₃ τ₁ (e₁ c′) (λ m → CPSVal m))
      (λ c → κ (CPSVar c))
  ⟶⟨ eqLet₁ (λ c → κ (CPSVar c)) (eqLet₁ (λ c′ → cpsI τ₃ τ₃ τ₁ (e₁ c′) (λ m → CPSVal m))
        (eqFun (λ a′ → eqFun (λ κ′ → eqApp₂ (eqApp₁ (eqBeta (sVal (sFun (λ x →
           ekSubst′ {e₁ = λ x → pcontext-plug τ₀ p₂ (Val (Var x))}
                    {e₂ = pcontext-plug τ₀ p₂ (Val (Var a′))}
                    x (subst-context p₂ (Var a′))))))))))) ⟩
    CPSLet
      (CPSLet
        (CPSVal (CPSFun (λ a′ → CPSVal (CPSFun λ κ′ →
          CPSApp (CPSVal (CPSVar κ′))
                 (CPSApp
                   (CPSVal (CPSFun (λ k → cpsI′ τ₄ τ₄ τ (pcontext-plug τ₀ p₂ (Val (Var a′))) (CPSVar k))))
                   (CPSVal (CPSFun (λ a → (λ m → CPSVal m) (CPSVar a)))))))))
        λ c′ → cpsI τ₃ τ₃ τ₁ (e₁ c′) (λ m → CPSVal m))
      (λ c → κ (CPSVar c))
  ⟶⟨ eqLet₁ (λ c → κ (CPSVar c)) (eqLet₁ (λ c′ → cpsI τ₃ τ₃ τ₁ (e₁ c′) (λ m → CPSVal m))
        (eqFun (λ a′ → eqFun (λ κ′ → eqApp₂ (eqBeta (kSubst′ (pcontext-plug τ₀ p₂ (Val (Var a′))))))))) ⟩
    CPSLet
      (CPSLet
        (CPSVal (CPSFun (λ a′ → CPSVal (CPSFun λ κ′ →
          CPSApp (CPSVal (CPSVar κ′))
                 (cpsI′ τ₄ τ₄ τ (pcontext-plug τ₀ p₂ (Val (Var a′)))
                        (CPSFun (λ a → (λ m → CPSVal m) (CPSVar a))))))))
        λ c′ → cpsI τ₃ τ₃ τ₁ (e₁ c′) (λ m → CPSVal m))
      (λ c → κ (CPSVar c))
  ⟶⟨ eqLet₁ (λ c → κ (CPSVar c)) (eqLet₁ (λ c′ → cpsI τ₃ τ₃ τ₁ (e₁ c′) (λ m → CPSVal m))
        (eqFun (λ a′ → eqFun (λ κ′ → eqApp₂
          (cpsEtaEta′ (pcontext-plug τ₀ p₂ (Val (Var a′))) (λ m → CPSVal m) (λ v → sVal sVar=)))))) ⟩
    CPSLet (CPSLet (CPSVal (CPSFun (λ a′ → CPSVal (CPSFun λ κ′ →
                      CPSApp (CPSVal (CPSVar κ′))
                             (cpsI τ₄ τ₄ τ (pcontext-plug τ₀ p₂ (Val (Var a′))) (λ m → CPSVal m))))))
                   λ c′ → cpsI τ₃ τ₃ τ₁ (e₁ c′) (λ m → CPSVal m))
      (λ c → κ (CPSVar c))
  ≡⟨ refl ⟩
    CPSLet (CPSLet (CPSVal (CPSFun (λ x′ → CPSVal (CPSFun (λ k′ →
                      CPSApp (CPSVal (CPSVar k′))
                             (cpsI τ₄ τ₄ τ (pcontext-plug τ₀ p₂ (Val (Var x′))) (λ m → CPSVal m)))))))
                   λ c₁ → cpsI τ₃ τ₃ τ₁ (e₁ c₁) (λ m → CPSVal m))
           (λ c → κ (CPSVar c))
  ⟵⟨ eqLet₁ (λ c → κ (CPSVar c)) (eqLet₁ (λ c₁ → cpsI τ₃ τ₃ τ₁ (e₁ c₁) (λ m → CPSVal m))
        (eqFun (λ x′ → eqFun (λ k′ → {!eqLetApp!})))) ⟩
    CPSLet (CPSLet (CPSVal (CPSFun (λ x′ → CPSVal (CPSFun λ k′ →
                      CPSLet (cpsI τ₄ τ₄ τ (pcontext-plug τ₀ p₂ (Val (Var x′))) (λ m → CPSVal m))
                             (λ c₂ → CPSApp (CPSVal (CPSVar k′)) (CPSVal (CPSVar c₂)))))))
                   λ c₁ → cpsI τ₃ τ₃ τ₁ (e₁ c₁) (λ m → CPSVal m))
           (λ c → κ (CPSVar c))
  ⟵⟨ eqLet₁ (λ c → κ (CPSVar c)) (eqLet₂
        (CPSVal (CPSFun (λ x′ → CPSVal (CPSFun (λ k′ →
                 CPSLet (cpsI τ₄ τ₄ τ (pcontext-plug τ₀ p₂ (Val (Var x′))) (λ m → CPSVal m))
                        (λ c₂ → CPSApp (CPSVal (CPSVar k′)) (CPSVal (CPSVar c₂))))))))
        λ c₁ → cpsEtaEta′ (e₁ c₁) (λ m → CPSVal m) λ v → sVal sVar=) ⟩
    CPSLet (CPSLet (CPSVal (CPSFun (λ x′ → CPSVal (CPSFun λ k′ →
                      CPSLet (cpsI τ₄ τ₄ τ (pcontext-plug τ₀ p₂ (Val (Var x′))) (λ m → CPSVal m))
                             (λ c₂ → CPSApp (CPSVal (CPSVar k′)) (CPSVal (CPSVar c₂)))))))
                   (λ c₁ → cpsI′ τ₃ τ₃ τ₁ (e₁ c₁) (CPSFun (λ a → (λ m → CPSVal m) (CPSVar a))) ))
           (λ c → κ (CPSVar c))
  ⟵⟨ eqLet₁ (λ c → κ (CPSVar c)) (eqLet₂
        (CPSVal (CPSFun (λ x′ → CPSVal (CPSFun (λ k′ →
                CPSLet (cpsI τ₄ τ₄ τ (pcontext-plug τ₀ p₂ (Val (Var x′))) (λ m → CPSVal m))
                       (λ c₂ → CPSApp (CPSVal (CPSVar k′)) (CPSVal (CPSVar c₂))))))))
        λ c₁ → eqBeta (kSubst′ (e₁ c₁))) ⟩
    CPSLet (CPSLet (CPSVal (CPSFun (λ x′ → CPSVal (CPSFun λ k′ →
                      CPSLet (cpsI τ₄ τ₄ τ (pcontext-plug τ₀ p₂ (Val (Var x′))) (λ m → CPSVal m))
                             (λ c₂ → CPSApp (CPSVal (CPSVar k′)) (CPSVal (CPSVar c₂)))))))
                   (λ c₁ → CPSApp
                            (CPSVal (CPSFun (λ k₁ → cpsI′ τ₃ τ₃ τ₁ (e₁ c₁) (CPSVar k₁))))
                            (CPSVal (CPSFun λ a → (λ m → CPSVal m) (CPSVar a)))))
           (λ c → κ (CPSVar c))
  ≡⟨ refl ⟩
    CPSLet (CPSLet (CPSVal (CPSFun (λ x′ → CPSVal (CPSFun (λ k′ →
                      cpsI′ τ α α (Reset τ₄ τ α (pcontext-plug τ₀ p₂ (Val (Var x′)))) (CPSVar k′))))))
                   (λ c₁ → CPSApp
                            (CPSVal (CPSFun (λ k₁ → cpsI′ τ₃ τ₃ τ₁ (e₁ c₁) (CPSVar k₁))))
                            (CPSVal (CPSFun λ a → (λ m → CPSVal m) (CPSVar a)))))
           (λ c → κ (CPSVar c))
  ⟵⟨ eqLet₁ (λ c → κ (CPSVar c)) eqLet₃ ⟩
    CPSLet (CPSApp
             (CPSLet (CPSVal (CPSFun (λ x′ → CPSVal (CPSFun (λ k′ →
                        cpsI′ τ α α (Reset τ₄ τ α (pcontext-plug τ₀ p₂ (Val (Var x′)))) (CPSVar k′))))))
                     (λ c₁ → CPSVal (CPSFun (λ k₁ → cpsI′ τ₃ τ₃ τ₁ (e₁ c₁) (CPSVar k₁)))))
             (CPSVal (CPSFun λ a → (λ m → CPSVal m) (CPSVar a))))
           (λ c → κ (CPSVar c))
  ⟶⟨ eqLet₁ (λ c → κ (CPSVar c)) (eqApp₁ eqLetApp) ⟩
    CPSLet (CPSApp
             (CPSApp (CPSVal (CPSFun (λ c₁ → CPSVal (CPSFun (λ k₁ → cpsI′ τ₃ τ₃ τ₁ (e₁ c₁) (CPSVar k₁))))))
                     (CPSVal (CPSFun (λ x′ → CPSVal (CPSFun (λ k′ →
                       cpsI′ τ α α (Reset τ₄ τ α (pcontext-plug τ₀ p₂ (Val (Var x′)))) (CPSVar k′)))))))
             (CPSVal (CPSFun λ a → (λ m → CPSVal m) (CPSVar a))))
           (λ c → κ (CPSVar c))
  ≡⟨ refl ⟩
    CPSLet (cpsI (τ₀ ⇒ τ cps[ α , α ]) τ₁ τ₁
             (Val (Fun τ τ₀ (λ x → Reset τ₄ τ α (pcontext-plug τ₀ p₂ (Val (Var x))))))
             (λ n → CPSApp
                      (CPSApp (CPSVal (CPSFun (λ c₁ → CPSVal (CPSFun (λ k₁ → cpsI′ τ₃ τ₃ τ₁ (e₁ c₁) (CPSVar k₁))))))
                              (CPSVal n))
                      (CPSVal (CPSFun λ a → (λ m → CPSVal m) (CPSVar a)))))
           (λ c → κ (CPSVar c))
  ≡⟨ refl ⟩
    CPSLet ((λ m → cpsI (τ₀ ⇒ τ cps[ α , α ]) τ₁ τ₁
                     (Val (Fun τ τ₀
                          (λ x → Reset τ₄ τ α (pcontext-plug τ₀ p₂ (Val (Var x))))))
                     (λ n → CPSApp (CPSApp (CPSVal m) (CPSVal n)) (CPSVal (CPSFun λ a → (λ m → CPSVal m) (CPSVar a)))))
            (CPSFun (λ c₁ → CPSVal (CPSFun (λ k₁ → cpsI′ τ₃ τ₃ τ₁ (e₁ c₁) (CPSVar k₁))))))
           (λ c → κ (CPSVar c))
  ≡⟨ refl ⟩
    CPSLet ((λ m → cpsI (τ₀ ⇒ τ cps[ α , α ]) τ₁ τ₁
                     (Val (Fun τ τ₀
                          (λ x → Reset τ₄ τ α (pcontext-plug τ₀ p₂ (Val (Var x))))))
                     (λ n → CPSApp (CPSApp (CPSVal m) (CPSVal n)) (CPSVal (CPSFun λ a → (λ m → CPSVal m) (CPSVar a)))))
            (cpsV ((τ₀ ⇒ τ cps[ α , α ]) ⇒ τ₃ cps[ τ₃ , τ₁ ]) (Fun τ₃ (τ₀ ⇒ τ cps[ α , α ]) e₁)))
           (λ c → κ (CPSVar c))
  ≡⟨ refl ⟩
    CPSLet (cpsI ((τ₀ ⇒ τ cps[ α , α ]) ⇒ τ₃ cps[ τ₃ , τ₁ ]) τ₁ τ₁
             (Val (Fun τ₃ (τ₀ ⇒ τ cps[ α , α ]) e₁))
             (λ m → cpsI (τ₀ ⇒ τ cps[ α , α ]) τ₁ τ₁
                      (Val (Fun τ τ₀
                           (λ x → Reset τ₄ τ α (pcontext-plug τ₀ p₂ (Val (Var x))))))
                      λ n → CPSApp (CPSApp (CPSVal m) (CPSVal n)) (CPSVal (CPSFun λ a → (λ m → CPSVal m) (CPSVar a)))))
           (λ c → κ (CPSVar c))
  ≡⟨ refl ⟩
    CPSLet (cpsI τ₃ τ₃ τ₁
             (App (Val (Fun τ₃ (τ₀ ⇒ τ cps[ α , α ]) e₁))
                  (Val (Fun τ τ₀
                       (λ x → Reset τ₄ τ α (pcontext-plug τ₀ p₂ (Val (Var x)))))))
             (λ m → CPSVal m))
           (λ c → κ (CPSVar c))
  ≡⟨ refl ⟩
    cpsI τ₁ τ₂ τ₂
      (Reset τ₃ τ₁ τ₂ (App (Val (Fun τ₃ (τ₀ ⇒ τ cps[ α , α ]) e₁))
                             (Val (Fun τ τ₀
                                  (λ x → Reset τ₄ τ α (pcontext-plug τ₀ p₂ (Val (Var x))))))))
      κ
  ∎
