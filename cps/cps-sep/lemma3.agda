module lemma3 where

open import DSterm
open import CPSterm
open import lemma1
open import lemma2

open import Function
open import Relation.Binary.PropositionalEquality

correctContI : {var : cpstyp → Set} → {τ₁ τ₂ τ₃ : typ} →
               {e₁ : term[ var ∘ cpsT ] τ₁ cps[ τ₂ , τ₃ ]} →
               (κ₁ : cpsvalue[ var ] (cpsT τ₁) → cpsterm[ var ] (cpsT τ₂)) →
               (κ₂ : cpsvalue[ var ] (cpsT τ₁) → cpsterm[ var ] (cpsT τ₂)) →
               schematic {var} {τ₁} {τ₂} κ₁ →
               schematic {var} {τ₁} {τ₂} κ₂ →
               ((v : value[ var ∘ cpsT ] τ₁ cps[τ,τ]) →
                cpsequal (κ₁ (cpsV τ₁ v)) (κ₂ (cpsV τ₁ v))) →
               cpsequal (cpsI τ₁ τ₂ τ₃ e₁ κ₁) (cpsI τ₁ τ₂ τ₃ e₁ κ₂)
correctContI {var} {τ₁} {τ₂} {.τ₂} {Val {τ₁ = .τ₁} {τ₂ = .τ₂} x} κ₁ κ₂ sche₁ sche₂ eq = eq x
correctContI {var} {τ₁} {τ₂} {τ₃}
             {App {τ₁ = .τ₁} {τ₂ = τ₄} {τ₃ = .τ₂} {τ₄ = τ₅} {τ₅ = τ₆} {τ₆ = .τ₃} e₁ e₂} κ₁ κ₂ sche₁ sche₂ eq =
  begin
    cpsI τ₁ τ₂ τ₃ (App e₁ e₂) κ₁
  ≡⟨ refl ⟩
    cpsI (τ₄ ⇒ τ₁ cps[ τ₂ , τ₅ ]) τ₆ τ₃ e₁
         (λ m → cpsI τ₄ τ₅ τ₆ e₂
                     λ n → CPSApp (CPSApp (CPSVal m) (CPSVal n)) (CPSVal (CPSFun (λ a → κ₁ (CPSVar a)))))
  ⟶⟨ correctContI {e₁ = e₁}
                    (λ m → cpsI τ₄ τ₅ τ₆ e₂
                                (λ n → CPSApp (CPSApp (CPSVal m) (CPSVal n)) (CPSVal (CPSFun (λ a → κ₁ (CPSVar a))))))
                    (λ m → cpsI τ₄ τ₅ τ₆ e₂
                                (λ n → CPSApp (CPSApp (CPSVal m) (CPSVal n)) (CPSVal (CPSFun (λ a → κ₂ (CPSVar a))))))
                    (λ x → κSubst e₂ (λ v → λ n → CPSApp (CPSApp (CPSVal v) (CPSVal n)) (CPSVal (CPSFun (λ a → κ₁ (CPSVar a)))))
                                   λ x₁ → sApp (sApp (sVal sVar=) Subst≠) (sVal (sFun (λ a → Subst≠))))
                    (λ x → κSubst e₂ (λ v → λ n → CPSApp (CPSApp (CPSVal v) (CPSVal n)) (CPSVal (CPSFun (λ a → κ₂ (CPSVar a)))))
                                   λ x₁ → sApp (sApp (sVal sVar=) Subst≠) (sVal (sFun (λ a → Subst≠))))
                    (λ v → correctContI {e₁ = e₂}
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
    cpsI τ₁ τ₂ τ₃ (App e₁ e₂) κ₂
  ∎
correctContI {var} {.τ₂} {.τ₃} {τ₃} {Reset τ₁ τ₂ τ₃ e₁} κ₁ κ₂ sche₁ sche₂ eq =
  eqLet₂ (cpsI τ₁ τ₁ τ₂ e₁ (λ m → CPSVal m)) (λ x → eq (Var x))
  
correctContI {var} {.τ₃} {.τ₄} {.τ₂} {Shift τ τ₁ τ₂ τ₃ τ₄ e₁} κ₁ κ₂ sche₁ sche₂ eq =
  eqLet₁ (λ c → cpsI τ₁ τ₁ τ₂ (e₁ c) λ m → CPSVal m)
         (eqFun (λ a → eqFun (λ κ′ → eqApp₂ (eq (Var a)))))

subst-context : {var : typ → Set} {τ₂ τ₃ τ₄ τ₀ : typ} →
                (con : pcontext[ var , τ₀ cps[ τ₂ , τ₂ ]] τ₄ cps[ τ₃ , τ₂ ]) →
                (v : value[ var ] τ₀ cps[τ,τ]) →
                Subst (λ x → pcontext-plug τ₀ con (Val (Var x)))
                      v
                      (pcontext-plug τ₀ con (Val v))
subst-context {var} {τ₂} {.τ₂} {τ₄} {.τ₄} (Hole {τ₁ = .τ₄} {τ₂ = .τ₂} {τ₃ = .τ₂}) v = sVal sVar=
subst-context {var} {τ₂} {τ₃} {τ₄} {τ₀}
              (Frame {τ₁ = .τ₀} {τ₂ = .τ₂} {τ₃ = .τ₂}
                     {τ₄ = .(τ₅ ⇒ τ₄ cps[ τ₃ , τ₇ ])} {τ₅ = τ₆} {τ₆ = .τ₄} {τ₇ = .τ₃}
                     (App₁ {τ₁ = .τ₄} {τ₂ = τ₅} {τ₃ = .τ₃} {τ₄ = τ₇} {τ₅ = .τ₆} {τ₆ = .τ₂} e₂) con′)
              v = sApp (subst-context con′ v) pSubst≠
subst-context {var} {τ₂} {τ₃} {τ₄} {τ₀}
              (Frame {τ₁ = .τ₀} {τ₂ = .τ₂} {τ₃ = .τ₂} {τ₄ = τ₅} {τ₅ = τ₆} {τ₆ = .τ₄} {τ₇ = .τ₃}
                     (App₂ {τ₁ = .τ₄} {τ₂ = .τ₅} {τ₃ = .τ₃} {τ₄ = .τ₆} {τ₅ = .τ₂} v₁) con′)
              v = sApp (sVal pSubstV≠) (subst-context con′ v) 
              

shift-lemma : ∀ {τ τ₁ τ₂ τ₃ τ₄ τ₅ α} {var : cpstyp → Set}
                (p₁ : pcontext[ var ∘ cpsT , τ₁ cps[ τ₂ , τ₃ ]]
                      τ₄ cps[ τ₅ , τ₃ ])
                (p₂ : pcontext[ var ∘ cpsT , τ₁ cps[ τ₂ , τ₂ ]]
                      τ₄ cps[ τ₅ , τ₂ ]) →
                same-pcontext p₁ p₂ →
                (e₁ : var (cpsT (τ₁ ⇒ τ₂ cps[ α , α ])) →
                   term[ var ∘ cpsT ] τ cps[ τ , τ₃ ])
                (κ : cpsvalue[ var ] (cpsT τ₄) → cpsterm[ var ] (cpsT τ₅))
                (sch : schematic {var} {τ₄} {τ₅} κ) →
                cpsequal (cpsI τ₄ τ₅ τ₃
                          (pcontext-plug τ₁ p₁ (Shift α τ τ₃ τ₁ τ₂ e₁)) κ)
                         (cpsI τ₄ τ₅ τ₃
                           (App (Val (Fun τ₄ τ₁
                                     (λ x → pcontext-plug τ₁ p₂ (Val (Var x)))))
                                            (Shift α τ τ₃ τ₁ τ₂ e₁)) κ)
shift-lemma {τ} {τ₁} {τ₂} {τ₃} {.τ₁} {.τ₂} {α} {var}
  .(Hole {_} {τ₁} {τ₂} {τ₃})
  .(Hole {_} {τ₁} {τ₂} {τ₂})
  Hole
  e₁ κ sch =
  begin
    cpsI τ₁ τ₂ τ₃ (pcontext-plug τ₁ Hole (Shift α τ τ₃ τ₁ τ₂ e₁)) κ
  ≡⟨ refl ⟩
    cpsI τ₁ τ₂ τ₃ (Shift α τ τ₃ τ₁ τ₂ e₁) κ
  ≡⟨ refl ⟩
    CPSLet (CPSVal (CPSFun (λ a → CPSVal (CPSFun
                           (λ κ′ →
                           CPSApp (CPSVal (CPSVar κ′)) (κ (CPSVar a)))))))
           (λ c → cpsI τ τ τ₃ (e₁ c) (λ m → CPSVal m))
  ⟵⟨ eqLet₁ (λ x → cpsI τ τ τ₃ (e₁ x) λ m → CPSVal m)
             (eqFun (λ x → eqFun (λ x₁ → eqApp₂ (eqBeta (sch (CPSVar x)))))) ⟩
    CPSLet (CPSVal (CPSFun (λ a → CPSVal (CPSFun
                           (λ κ′ →
                           CPSApp (CPSVal (CPSVar κ′))
                                  (CPSApp (CPSVal (CPSFun (λ v → κ (CPSVar v))))
                                          (CPSVal (CPSVar a)))))))) 
           (λ c → cpsI τ τ τ₃ (e₁ c) (λ m → CPSVal m))
  ⟵⟨ eqLet₁ (λ x → cpsI τ τ τ₃ (e₁ x) (λ m → CPSVal m))
              (eqFun (λ x → eqFun (λ x₁ → eqApp₂ (eqBeta (sApp (sVal sVar=) (sVal sVar≠)))))) ⟩
    CPSLet (CPSVal (CPSFun (λ a → CPSVal (CPSFun
                           (λ κ′ →
                           CPSApp (CPSVal (CPSVar κ′))
                                  (CPSApp (CPSVal (CPSFun (λ k → CPSApp (CPSVal (CPSVar k))
                                                                         (CPSVal (CPSVar a)))))
                                          (CPSVal (CPSFun λ v → κ (CPSVar v)))))))))
           (λ c → cpsI τ τ τ₃ (e₁ c) (λ m → CPSVal m))
  ⟵⟨ eqLet₁ (λ x → cpsI τ τ τ₃ (e₁ x) (λ m → CPSVal m))
              (eqFun (λ x → eqFun (λ x₁ → eqApp₂ (eqApp₁ (eqBeta (sVal (sFun (λ x → sApp (sVal sVar≠) (sVal sVar=))))))))) ⟩
    CPSLet (CPSVal (CPSFun (λ a → CPSVal (CPSFun
                           (λ κ′ →
                           CPSApp (CPSVal (CPSVar κ′))
                                  (CPSApp (CPSApp (CPSVal (CPSFun (λ x → CPSVal (CPSFun
                                                                  (λ k → CPSApp (CPSVal (CPSVar k))
                                                                                 (CPSVal (CPSVar x)))))))
                                                  (CPSVal (CPSVar a)))
                                          (CPSVal (CPSFun (λ v → κ (CPSVar v))))))))))
           (λ c → cpsI τ τ τ₃ (e₁ c) (λ m → CPSVal m))
  ≡⟨ refl ⟩
    CPSLet (CPSVal (CPSFun (λ a → CPSVal (CPSFun
                           (λ κ′ →
                           CPSApp (CPSVal (CPSVar κ′))
                                  (CPSApp (CPSApp (CPSVal (CPSFun (λ x → CPSVal (CPSFun
                                                                  (λ k → cpsI′ τ₁ τ₂ τ₂ (Val (Var x)) (CPSVar k))))))
                                                  (CPSVal (CPSVar a)))
                                          (CPSVal (CPSFun (λ v → κ (CPSVar v))))))))))
           (λ c → cpsI τ τ τ₃ (e₁ c) (λ m → CPSVal m))
  ≡⟨ refl ⟩
    CPSLet (CPSVal (CPSFun (λ a → CPSVal (CPSFun
                           (λ κ′ →
                           CPSApp (CPSVal (CPSVar κ′))
                                  (CPSApp (CPSApp (CPSVal (CPSFun (λ x → CPSVal (CPSFun
                                                                  (λ k → cpsI′ τ₁ τ₂ τ₂
                                                                               (pcontext-plug τ₁ Hole (Val (Var x)))
                                                                               (CPSVar k))))))
                                                  (CPSVal (CPSVar a)))
                                          (CPSVal (CPSFun (λ v → κ (CPSVar v))))))))))
           (λ c → cpsI τ τ τ₃ (e₁ c) (λ m → CPSVal m))
  ≡⟨ refl ⟩
    CPSLet (CPSVal (CPSFun (λ a → CPSVal (CPSFun
                           (λ κ′ →
                           CPSApp (CPSVal (CPSVar κ′))
                                  ((λ n → CPSApp (CPSApp (CPSVal (CPSFun (λ x → CPSVal (CPSFun
                                                                          (λ k → cpsI′ τ₁ τ₂ τ₂
                                                                                        (pcontext-plug τ₁ Hole (Val (Var x))) (
                                                                                        CPSVar k))))))
                                                          (CPSVal n))
                                                  (CPSVal (CPSFun (λ v → κ (CPSVar v)))))
                                   (CPSVar a)))))))
           (λ c → cpsI τ τ τ₃ (e₁ c) (λ m → CPSVal m))
  ≡⟨ refl ⟩
    cpsI τ₁ τ₂ τ₃
         (Shift α τ τ₃ τ₁ τ₂ e₁)
         (λ n → CPSApp (CPSApp (CPSVal (CPSFun (λ x → CPSVal (CPSFun
                                                (λ k → cpsI′ τ₁ τ₂ τ₂
                                                             (pcontext-plug τ₁ Hole (Val (Var x)))
                                                             (CPSVar k))))))
                                (CPSVal n))
                        (CPSVal (CPSFun (λ v → κ (CPSVar v)))))
  ≡⟨ refl ⟩
    cpsI τ₁ τ₂ τ₃
         (Shift α τ τ₃ τ₁ τ₂ e₁)
         (λ n → CPSApp (CPSApp (CPSVal (cpsV (τ₁ ⇒ τ₁ cps[ τ₂ , τ₂ ])
                                             (Fun τ₁ τ₁ (λ x → pcontext-plug τ₁ Hole (Val (Var x))))))
                                (CPSVal n))
                        (CPSVal (CPSFun (λ v → κ (CPSVar v)))))
  ≡⟨ refl ⟩
    (λ m → cpsI τ₁ τ₂ τ₃
                 (Shift α τ τ₃ τ₁ τ₂ e₁)
                 λ n → CPSApp (CPSApp (CPSVal m) (CPSVal n))
                               (CPSVal (CPSFun (λ v → κ (CPSVar v)))))
    (cpsV (τ₁ ⇒ τ₁ cps[ τ₂ , τ₂ ])
          (Fun τ₁ τ₁ (λ x → pcontext-plug τ₁ Hole (Val (Var x)))))
  ≡⟨ refl ⟩
    cpsI (τ₁ ⇒ τ₁ cps[ τ₂ , τ₂ ]) τ₃ τ₃
         (Val (Fun τ₁ τ₁ (λ x → pcontext-plug τ₁ Hole (Val (Var x)))))
         (λ m → cpsI τ₁ τ₂ τ₃
                      (Shift α τ τ₃ τ₁ τ₂ e₁)
                      λ n → CPSApp (CPSApp (CPSVal m) (CPSVal n))
                                   (CPSVal (CPSFun λ a → κ (CPSVar a))))
  ⟵⟨ eqId ⟩
    cpsI τ₁ τ₂ τ₃
      (App (Val (Fun τ₁ τ₁ (λ x → pcontext-plug τ₁ Hole (Val (Var x)))))
           (Shift α τ τ₃ τ₁ τ₂ e₁))
      κ
  ∎   

shift-lemma {τ} {τ₁} {τ₂} {τ₃} {τ₄} {τ₅} {α} {var}
            .(Frame {_} {τ₁} {τ₂} {τ₃} {τ₆ ⇒ τ₄ cps[ τ₅ , τ₈ ]} {τ₇} {τ₄} {τ₅}
              (App₁ {_} {τ₄} {τ₆} {τ₅} {τ₈} {τ₇} {τ₃} e₂) p₁′)
            .(Frame {_} {τ₁} {τ₂} {τ₂} {τ₆ ⇒ τ₄ cps[ τ₅ , τ₈ ]} {τ₇} {τ₄} {τ₅}
              (App₁ {_} {τ₄} {τ₆} {τ₅} {τ₈} {τ₇} {τ₂} e₂) p₂′)
             (Frame {τ₄ = .(τ₆ ⇒ τ₄ cps[ τ₅ , τ₈ ])} {τ₅ = τ₇} {τ₆ = .τ₄} {τ₇ = .τ₅}
               {f₁ = App₁ {τ₁ = .τ₄} {τ₂ = τ₆} {τ₃ = .τ₅} {τ₄ = τ₈} {τ₅ = .τ₇} {τ₆ = .τ₃} e₂}
               {f₂ = App₁ {τ₁ = .τ₄} {τ₂ = .τ₆} {τ₃ = .τ₅} {τ₄ = .τ₈} {τ₅ = .τ₇} {τ₆ = .τ₂} .e₂}
               (App₁ {τ₂ = .τ₆} {τ₄ = .τ₈} {τ₆ = .τ₂} .e₂) {p₁ = p₁′} {p₂ = p₂′} c)
             e₁ κ sch =
  begin
    cpsI τ₄ τ₅ τ₃
      (pcontext-plug τ₁ (Frame (App₁ e₂) p₁′) (Shift α τ τ₃ τ₁ τ₂ e₁)) κ
  ≡⟨ refl ⟩
    cpsI τ₄ τ₅ τ₃
         (pframe-plug (App₁ e₂) (pcontext-plug τ₁ p₁′ (Shift α τ τ₃ τ₁ τ₂ e₁))) κ
  ≡⟨ refl ⟩
    cpsI τ₄ τ₅ τ₃
         (App (pcontext-plug τ₁ p₁′ (Shift α τ τ₃ τ₁ τ₂ e₁)) e₂)
         κ
  ≡⟨ refl ⟩
    cpsI (τ₆ ⇒ τ₄ cps[ τ₅ , τ₈ ]) τ₇ τ₃
         (pcontext-plug τ₁ p₁′ (Shift α τ τ₃ τ₁ τ₂ e₁))
         (λ m → cpsI τ₆ τ₈ τ₇ e₂
                     (λ n → CPSApp (CPSApp (CPSVal m) (CPSVal n))
                                    (CPSVal (CPSFun (λ a → κ (CPSVar a))))))
  ⟷⟨ shift-lemma p₁′ p₂′ c e₁ (λ m → cpsI τ₆ τ₈ τ₇ e₂
                               (λ n → CPSApp (CPSApp (CPSVal m) (CPSVal n))
                                             (CPSVal (CPSFun (λ a → κ (CPSVar a))))))
                              (λ v → κSubst e₂ (λ y → λ n → CPSApp (CPSApp (CPSVal y) (CPSVal n))
                                                                     (CPSVal (CPSFun (λ v → κ (CPSVar v)))))
                                             λ x → sApp (sApp (sVal sVar=) Subst≠) Subst≠) ⟩
    cpsI (τ₆ ⇒ τ₄ cps[ τ₅ , τ₈ ]) τ₇ τ₃
         (App (Val (Fun (τ₆ ⇒ τ₄ cps[ τ₅ , τ₈ ]) τ₁
                        (λ x → pcontext-plug τ₁ p₂′ (Val (Var x)))))
                        (Shift α τ τ₃ τ₁ τ₂ e₁))
         (λ m → cpsI τ₆ τ₈ τ₇ e₂
                     (λ n → CPSApp (CPSApp (CPSVal m) (CPSVal n))
                                   (CPSVal (CPSFun (λ v → κ (CPSVar v))))))
  ≡⟨ refl ⟩
    cpsI (τ₁ ⇒ τ₆ ⇒ τ₄ cps[ τ₅ , τ₈ ] cps[ τ₇ , τ₂ ]) τ₃ τ₃
         (Val (Fun (τ₆ ⇒ τ₄ cps[ τ₅ , τ₈ ]) τ₁ (λ x → pcontext-plug τ₁ p₂′ (Val (Var x)))))
         (λ m′ → cpsI τ₁ τ₂ τ₃
                     (Shift α τ τ₃ τ₁ τ₂ e₁)
                     (λ n′ → CPSApp (CPSApp (CPSVal m′) (CPSVal n′))
                                   (CPSVal (CPSFun (λ a₁ → cpsI τ₆ τ₈ τ₇ e₂
                                                          (λ n → CPSApp (CPSApp (CPSVal (CPSVar a₁)) (CPSVal n))
                                                                        (CPSVal (CPSFun (λ v → κ (CPSVar v))))))))))
  ≡⟨ refl ⟩
    (λ m′ → cpsI τ₁ τ₂ τ₃
                (Shift α τ τ₃ τ₁ τ₂ e₁)
                (λ n′ → CPSApp (CPSApp (CPSVal m′) (CPSVal n′))
                               (CPSVal (CPSFun (λ a₁ → cpsI τ₆ τ₈ τ₇ e₂
                                                             (λ n → CPSApp (CPSApp (CPSVal (CPSVar a₁)) (CPSVal n))
                                                                           (CPSVal (CPSFun (λ v → κ (CPSVar v))))))))))
    (cpsV (τ₁ ⇒ τ₆ ⇒ τ₄ cps[ τ₅ , τ₈ ] cps[ τ₇ , τ₂ ])
          (Fun (τ₆ ⇒ τ₄ cps[ τ₅ , τ₈ ]) τ₁
          (λ x → pcontext-plug τ₁ p₂′ (Val (Var x)))))
  ≡⟨ refl ⟩
    (λ m′ → cpsI τ₁ τ₂ τ₃
                (Shift α τ τ₃ τ₁ τ₂ e₁)
                (λ n′ → CPSApp (CPSApp (CPSVal m′) (CPSVal n′))
                               (CPSVal (CPSFun (λ a₁ → cpsI τ₆ τ₈ τ₇ e₂
                                                             (λ n → CPSApp (CPSApp (CPSVal (CPSVar a₁)) (CPSVal n))
                                                                            (CPSVal (CPSFun (λ v → κ (CPSVar v))))))))))
    (CPSFun (λ x → CPSVal (CPSFun (λ k →
            cpsI′ (τ₆ ⇒ τ₄ cps[ τ₅ , τ₈ ]) τ₇ τ₂ (pcontext-plug τ₁ p₂′ (Val (Var x))) (CPSVar k)))))

  ≡⟨ refl ⟩
    cpsI τ₁ τ₂ τ₃
         (Shift α τ τ₃ τ₁ τ₂ e₁)
         (λ n′ → CPSApp (CPSApp (CPSVal (CPSFun (λ x → CPSVal (CPSFun (λ k →
                                                cpsI′ (τ₆ ⇒ τ₄ cps[ τ₅ , τ₈ ]) τ₇ τ₂
                                                      (pcontext-plug τ₁ p₂′ (Val (Var x))) (CPSVar k))))))
                                (CPSVal n′))
                        (CPSVal (CPSFun (λ a₁ → cpsI τ₆ τ₈ τ₇ e₂
                                                     (λ n → CPSApp (CPSApp (CPSVal (CPSVar a₁)) (CPSVal n))
                                                                   (CPSVal (CPSFun (λ v → κ (CPSVar v)))))))))
  ≡⟨ refl ⟩
    CPSLet (CPSVal (CPSFun λ a → CPSVal (CPSFun (λ κ′ →
           CPSApp (CPSVal (CPSVar κ′))
                  (CPSApp (CPSApp (CPSVal (CPSFun (λ x → CPSVal (CPSFun (λ k →
                                          cpsI′ (τ₆ ⇒ τ₄ cps[ τ₅ , τ₈ ]) τ₇ τ₂
                                                (pcontext-plug τ₁ p₂′ (Val (Var x))) (CPSVar k))))))
                                  (CPSVal (CPSVar a)))
                          (CPSVal (CPSFun (λ a₁ → cpsI τ₆ τ₈ τ₇ e₂
                                          (λ n → CPSApp (CPSApp (CPSVal (CPSVar a₁)) (CPSVal n))
                                                         (CPSVal (CPSFun (λ v → κ (CPSVar v)))))))))))))
           (λ c → cpsI τ τ τ₃ (e₁ c) (λ m → CPSVal m))
  ⟶⟨ eqLet₁ (λ c → cpsI τ τ τ₃ (e₁ c) (λ m → CPSVal m))
              (eqFun (λ a → eqFun (λ κ′ → eqApp₂ (eqApp₁ (eqBeta (sVal (sFun (λ k →
              ekSubst′ {e₁ = λ x → pcontext-plug τ₁ p₂′ (Val (Var x))} {e₂ = pcontext-plug τ₁ p₂′ (Val (Var a))}
                       k (subst-context p₂′ (Var a)))))))))) ⟩
    CPSLet (CPSVal (CPSFun λ a → CPSVal (CPSFun (λ κ′ →
           CPSApp (CPSVal (CPSVar κ′))
                  (CPSApp (CPSVal (CPSFun (λ k → cpsI′ (τ₆ ⇒ τ₄ cps[ τ₅ , τ₈ ]) τ₇ τ₂
                                                 (pcontext-plug τ₁ p₂′ (Val (Var a))) (CPSVar k))))
                          (CPSVal (CPSFun (λ a₁ → cpsI τ₆ τ₈ τ₇ e₂
                                          (λ n → CPSApp (CPSApp (CPSVal (CPSVar a₁)) (CPSVal n))
                                                         (CPSVal (CPSFun (λ v → κ (CPSVar v)))))))))))))
           (λ c → cpsI τ τ τ₃ (e₁ c) (λ m → CPSVal m))
  ⟶⟨ eqLet₁ (λ c → cpsI τ τ τ₃ (e₁ c) (λ m → CPSVal m))
               (eqFun (λ a → eqFun (λ κ′ → eqApp₂ (eqBeta (kSubst′ (pcontext-plug τ₁ p₂′ (Val (Var a)))))))) ⟩
    CPSLet (CPSVal (CPSFun λ a → CPSVal (CPSFun (λ κ′ →
           CPSApp (CPSVal (CPSVar κ′))
                  (cpsI′ (τ₆ ⇒ τ₄ cps[ τ₅ , τ₈ ]) τ₇ τ₂ (pcontext-plug τ₁ p₂′ (Val (Var a)))
                  (CPSFun (λ a₁ → cpsI τ₆ τ₈ τ₇ e₂
                                       (λ n → CPSApp (CPSApp (CPSVal (CPSVar a₁)) (CPSVal n))
                                                     (CPSVal (CPSFun (λ v → κ (CPSVar v))))))))))))
           (λ c → cpsI τ τ τ₃ (e₁ c) (λ m → CPSVal m))
  ≡⟨ refl ⟩
    CPSLet (CPSVal (CPSFun λ a → CPSVal (CPSFun (λ κ′ →
           CPSApp (CPSVal (CPSVar κ′))
                  (cpsI′ (τ₆ ⇒ τ₄ cps[ τ₅ , τ₈ ]) τ₇ τ₂ (pcontext-plug τ₁ p₂′ (Val (Var a)))
                  (CPSFun (λ a₁ → (λ y → cpsI τ₆ τ₈ τ₇ e₂
                                               (λ n → CPSApp (CPSApp (CPSVal y) (CPSVal n))
                                                              (CPSVal (CPSFun (λ v → κ  (CPSVar v))))))
                                   (CPSVar a₁))))))))
           (λ c → cpsI τ τ τ₃ (e₁ c) (λ m → CPSVal m))
  ⟶⟨ eqLet₁ (λ c → cpsI τ τ τ₃ (e₁ c) (λ m → CPSVal m))
              (eqFun (λ a → eqFun (λ κ′ → eqApp₂
              (cpsEtaEta′ (pcontext-plug τ₁ p₂′ (Val (Var a)))
                          (λ y → cpsI τ₆ τ₈ τ₇ e₂
                                 (λ n → CPSApp (CPSApp (CPSVal y) (CPSVal n))
                                               (CPSVal (CPSFun (λ v → κ (CPSVar v))))))
                          λ v′ → κSubst e₂ (λ y → λ n → CPSApp (CPSApp (CPSVal y) (CPSVal n))
                                                                  (CPSVal (CPSFun (λ v → κ (CPSVar v)))))
                                        λ v′′ → sApp (sApp (sVal sVar=) Subst≠) (sVal (sFun (λ v → Subst≠))))))) ⟩
    CPSLet (CPSVal (CPSFun λ a → CPSVal (CPSFun (λ κ′ →
           CPSApp (CPSVal (CPSVar κ′))
                  (cpsI (τ₆ ⇒ τ₄ cps[ τ₅ , τ₈ ]) τ₇ τ₂ (pcontext-plug τ₁ p₂′ (Val (Var a)))
                        (λ y → cpsI τ₆ τ₈ τ₇ e₂
                                    (λ n → CPSApp (CPSApp (CPSVal y) (CPSVal n))
                                                   (CPSVal (CPSFun (λ v → κ (CPSVar v)))))))))))
           (λ c → cpsI τ τ τ₃ (e₁ c) (λ m → CPSVal m))

  ≡⟨ refl ⟩
    CPSLet (CPSVal (CPSFun (λ a → CPSVal (CPSFun (λ κ′ →
                     CPSApp (CPSVal (CPSVar κ′))
                            (cpsI (τ₆ ⇒ τ₄ cps[ τ₅ , τ₈ ]) τ₇ τ₂ (pcontext-plug τ₁ p₂′ (Val (Var a)))
                                  (λ m₁ → cpsI τ₆ τ₈ τ₇ e₂
                                                (λ n₁ → CPSApp (CPSApp (CPSVal m₁) (CPSVal n₁))
                                                                (CPSVal (CPSFun (λ v → κ (CPSVar v))))))))))))
           (λ c → cpsI τ τ τ₃ (e₁ c) (λ m → CPSVal m))

  ⟵⟨ eqLet₁ (λ c₁ → cpsI τ τ τ₃ (e₁ c₁) (λ m → CPSVal m))
              (eqFun (λ a → eqFun (λ κ′ → eqApp₂ (eqBeta
              (κSubst (pcontext-plug τ₁ p₂′ (Val (Var a)))
                       (λ k m₁ → cpsI τ₆ τ₈ τ₇ e₂
                                       (λ n₁ → CPSApp (CPSApp (CPSVal m₁) (CPSVal n₁)) (CPSVal k)))
                       λ x → κSubst e₂ (λ y n₁ → CPSApp (CPSApp (CPSVal x) (CPSVal n₁)) (CPSVal y))
                                     λ x₁ → sApp (sApp Subst≠ Subst≠) (sVal sVar=)))))) ⟩
    CPSLet (CPSVal (CPSFun (λ a → CPSVal (CPSFun (λ κ′ →
                     CPSApp (CPSVal (CPSVar κ′))
                            (CPSApp (CPSVal (CPSFun (λ k →
                                     cpsI (τ₆ ⇒ τ₄ cps[ τ₅ , τ₈ ]) τ₇ τ₂ (pcontext-plug τ₁ p₂′ (Val (Var a)))
                                          (λ m₁ → cpsI τ₆ τ₈ τ₇ e₂
                                                   (λ n₁ → CPSApp (CPSApp (CPSVal m₁) (CPSVal n₁))
                                                                   (CPSVal (CPSVar k)))))))
                                    (CPSVal (CPSFun (λ v → κ (CPSVar v))))))))))
           (λ c → cpsI τ τ τ₃ (e₁ c) (λ m → CPSVal m))
  ⟵⟨ eqLet₁ (λ c₁ → cpsI τ τ τ₃ (e₁ c₁) (λ m → CPSVal m))
              (eqFun (λ a → eqFun (λ κ′ → eqApp₂ (eqApp₁ (eqBeta (sVal (sFun (λ x →
              eSubst (subst-context p₂′ (Var a))
                     λ x₁ → eκSubst {e₁ = λ y → e₂} {e₂ = e₂} pSubst≠
                     λ x₂ → sApp (sApp (sVal x₁) (sVal x₂)) Subst≠)))))))) ⟩
    CPSLet (CPSVal (CPSFun (λ a → CPSVal (CPSFun (λ κ′ →
                     CPSApp (CPSVal (CPSVar κ′))
                            (CPSApp (CPSApp (CPSVal (CPSFun (λ x → CPSVal (CPSFun (λ k →
                                                    cpsI (τ₆ ⇒ τ₄ cps[ τ₅ , τ₈ ]) τ₇ τ₂
                                                         (pcontext-plug τ₁ p₂′ (Val (Var x)))
                                                         (λ m₁ → cpsI τ₆ τ₈ τ₇ e₂
                                                                 (λ n₁ → CPSApp (CPSApp (CPSVal m₁) (CPSVal n₁))
                                                                                (CPSVal (CPSVar k)))))))))
                                            (CPSVal (CPSVar a)))
                                    (CPSVal (CPSFun (λ v → κ (CPSVar v))))))))))
           (λ c → cpsI τ τ τ₃ (e₁ c) (λ m → CPSVal m))
  ≡⟨ refl ⟩
    cpsI τ₁ τ₂ τ₃
         (Shift α τ τ₃ τ₁ τ₂ e₁)
         (λ n → CPSApp (CPSApp (CPSVal (CPSFun (λ x → CPSVal (CPSFun (λ k →
                                       cpsI (τ₆ ⇒ τ₄ cps[ τ₅ , τ₈ ]) τ₇ τ₂ (pcontext-plug τ₁ p₂′ (Val (Var x)))
                                            (λ m₁ → cpsI τ₆ τ₈ τ₇ e₂
                                                    (λ n₁ → CPSApp (CPSApp (CPSVal m₁) (CPSVal n₁)) (CPSVal (CPSVar k)))))))))
                                (CPSVal n))
                        (CPSVal (CPSFun (λ v → κ (CPSVar v)))))
  ≡⟨ refl ⟩
    (λ m → cpsI τ₁ τ₂ τ₃
                 (Shift α τ τ₃ τ₁ τ₂ e₁)
                 (λ n → CPSApp (CPSApp (CPSVal m) (CPSVal n))
                                (CPSVal (CPSFun (λ v → κ (CPSVar v))))))
    (CPSFun (λ x → CPSVal (CPSFun (λ k →
    cpsI (τ₆ ⇒ τ₄ cps[ τ₅ , τ₈ ]) τ₇ τ₂ (pcontext-plug τ₁ p₂′ (Val (Var x)))
         (λ m₁ → cpsI τ₆ τ₈ τ₇ e₂
         (λ n₁ → CPSApp (CPSApp (CPSVal m₁) (CPSVal n₁)) (CPSVal (CPSVar k))))))))
  ≡⟨ refl ⟩
    (λ m → cpsI τ₁ τ₂ τ₃
                 (Shift α τ τ₃ τ₁ τ₂ e₁)
                 (λ n → CPSApp (CPSApp (CPSVal m) (CPSVal n))
                                (CPSVal (CPSFun (λ v → κ (CPSVar v))))))
    (CPSFun (λ x → CPSVal (CPSFun (λ k →
    cpsI′ τ₄ τ₅ τ₂ (App (pcontext-plug τ₁ p₂′ (Val (Var x))) e₂) (CPSVar k)))))
  ≡⟨ refl ⟩
    (λ m → cpsI τ₁ τ₂ τ₃
                 (Shift α τ τ₃ τ₁ τ₂ e₁)
                 (λ n → CPSApp (CPSApp (CPSVal m) (CPSVal n))
                                (CPSVal (CPSFun (λ v → κ (CPSVar v))))))
    (CPSFun (λ x → CPSVal (CPSFun (λ k →
    cpsI′ τ₄ τ₅ τ₂ (pframe-plug (App₁ e₂) (pcontext-plug τ₁ p₂′ (Val (Var x)))) (CPSVar k)))))
  ≡⟨ refl ⟩
    (λ m → cpsI τ₁ τ₂ τ₃
                 (Shift α τ τ₃ τ₁ τ₂ e₁)
                 (λ n → CPSApp (CPSApp (CPSVal m) (CPSVal n))
                                (CPSVal (CPSFun (λ v → κ (CPSVar v))))))
    (CPSFun (λ x → CPSVal (CPSFun (λ k →
    cpsI′ τ₄ τ₅ τ₂ (pcontext-plug τ₁ (Frame (App₁ e₂) p₂′) (Val (Var x))) (CPSVar k)))))
  ≡⟨ refl ⟩
    (λ m → cpsI τ₁ τ₂ τ₃
                 (Shift α τ τ₃ τ₁ τ₂ e₁)
                 (λ n → CPSApp (CPSApp (CPSVal m) (CPSVal n))
                                (CPSVal (CPSFun (λ v → κ (CPSVar v))))))
    (cpsV (τ₁ ⇒ τ₄ cps[ τ₅ , τ₂ ]) (Fun τ₄ τ₁ λ x → pcontext-plug τ₁ (Frame (App₁ e₂) p₂′) (Val (Var x))))
  ≡⟨ refl ⟩
    cpsI (τ₁ ⇒ τ₄ cps[ τ₅ , τ₂ ]) τ₃ τ₃
         (Val (Fun τ₄ τ₁ (λ x → pcontext-plug τ₁ (Frame (App₁ e₂) p₂′) (Val (Var x)))))
         (λ m → cpsI τ₁ τ₂ τ₃
                     (Shift α τ τ₃ τ₁ τ₂ e₁)
                     (λ n → CPSApp (CPSApp (CPSVal m) (CPSVal n))
                                    (CPSVal (CPSFun (λ v → κ (CPSVar v))))))
  ≡⟨ refl ⟩
    cpsI τ₄ τ₅ τ₃ (App (Val (Fun τ₄ τ₁ (λ x → pcontext-plug τ₁ (Frame (App₁ e₂) p₂′) (Val (Var x)))))
         (Shift α τ τ₃ τ₁ τ₂ e₁))
         κ
  ∎

shift-lemma {τ} {τ₁} {τ₂} {τ₃} {τ₄} {τ₅} {α} {var}
            .(Frame {_} {τ₁} {τ₂} {τ₃} {τ₆} {τ₇} {τ₄} {τ₅} (App₂ {_} {τ₄} {τ₆} {τ₅} {τ₇} {τ₃} v₁) p₁′)
            .(Frame {_} {τ₁} {τ₂} {τ₂} {τ₆} {τ₇} {τ₄} {τ₅} (App₂ {_} {τ₄} {τ₆} {τ₅} {τ₇} {τ₂} v₁) p₂′)
            (Frame {τ₄ = τ₆} {τ₅ = τ₇} {τ₆ = .τ₄} {τ₇ = .τ₅}
                   {f₁ = App₂ {τ₁ = .τ₄} {τ₂ = .τ₆} {τ₃ = .τ₅} {τ₄ = .τ₇} {τ₅ = .τ₃} v₁}
                   {f₂ = App₂ {τ₁ = .τ₄} {τ₂ = .τ₆} {τ₃ = .τ₅} {τ₄ = .τ₇} {τ₅ = .τ₂} .v₁}
                   (App₂ {τ₂ = .τ₆} {τ₆ = .τ₂} .v₁) {p₁ = p₁′} {p₂ = p₂′} c)
            e₁ κ sch =
  begin
    cpsI τ₄ τ₅ τ₃
      (pcontext-plug τ₁ (Frame (App₂ v₁) p₁′) (Shift α τ τ₃ τ₁ τ₂ e₁)) κ
  ≡⟨ refl ⟩
    cpsI τ₄ τ₅ τ₃
         (App (Val v₁) (pcontext-plug τ₁ p₁′ (Shift α τ τ₃ τ₁ τ₂ e₁)))
         κ
  ≡⟨ refl ⟩
    cpsI (τ₆ ⇒ τ₄ cps[ τ₅ , τ₇ ]) τ₃ τ₃ (Val v₁)
         (λ m → cpsI τ₆ τ₇ τ₃
                     (pcontext-plug τ₁ p₁′ (Shift α τ τ₃ τ₁ τ₂ e₁))
                     (λ n → CPSApp (CPSApp (CPSVal m) (CPSVal n)) (CPSVal (CPSFun (λ a → κ (CPSVar a))))))
  ≡⟨ refl ⟩
    (λ m → cpsI τ₆ τ₇ τ₃
                (pcontext-plug τ₁ p₁′ (Shift α τ τ₃ τ₁ τ₂ e₁))
                (λ n → CPSApp (CPSApp (CPSVal m) (CPSVal n)) (CPSVal (CPSFun (λ a → κ (CPSVar a))))))
    (cpsV (τ₆ ⇒ τ₄ cps[ τ₅ , τ₇ ]) v₁)
  ≡⟨ refl ⟩
    cpsI τ₆ τ₇ τ₃
         (pcontext-plug τ₁ p₁′ (Shift α τ τ₃ τ₁ τ₂ e₁))
         (λ n → CPSApp (CPSApp (CPSVal (cpsV (τ₆ ⇒ τ₄ cps[ τ₅ , τ₇ ]) v₁)) (CPSVal n)) (CPSVal (CPSFun (λ a → κ (CPSVar a)))))
  ⟷⟨ shift-lemma p₁′ p₂′ c e₁
                  (λ n → CPSApp (CPSApp (CPSVal (cpsV (τ₆ ⇒ τ₄ cps[ τ₅ , τ₇ ]) v₁)) (CPSVal n)) (CPSVal (CPSFun (λ a → κ (CPSVar a)))))
                  (λ v → sApp (sApp Subst≠ (sVal sVar=)) Subst≠) ⟩
    cpsI τ₆ τ₇ τ₃
         (App (Val (Fun τ₆ τ₁ (λ x → pcontext-plug τ₁ p₂′ (Val (Var x)))))
              (Shift α τ τ₃ τ₁ τ₂ e₁))
         (λ n → CPSApp (CPSApp (CPSVal (cpsV (τ₆ ⇒ τ₄ cps[ τ₅ , τ₇ ]) v₁)) (CPSVal n)) (CPSVal (CPSFun (λ a → κ (CPSVar a)))))
  ≡⟨ refl ⟩
    cpsI (τ₁ ⇒ τ₆ cps[ τ₇ , τ₂ ]) τ₃ τ₃
         (Val (Fun τ₆ τ₁ (λ x → pcontext-plug τ₁ p₂′ (Val (Var x)))))
         (λ m₁ → cpsI τ₁ τ₂ τ₃
                      (Shift α τ τ₃ τ₁ τ₂ e₁)
                      (λ n₁ → CPSApp (CPSApp (CPSVal m₁) (CPSVal n₁))
                                     (CPSVal (CPSFun (λ a₁ →
                                       CPSApp (CPSApp (CPSVal (cpsV (τ₆ ⇒ τ₄ cps[ τ₅ , τ₇ ]) v₁)) (CPSVal (CPSVar a₁)))
                                              (CPSVal (CPSFun (λ a → κ (CPSVar a)))))))))
  ≡⟨ refl ⟩
    (λ m₁ → cpsI τ₁ τ₂ τ₃
                (Shift α τ τ₃ τ₁ τ₂ e₁)
                (λ n₁ → CPSApp
                          (CPSApp (CPSVal m₁) (CPSVal n₁))
                          (CPSVal (CPSFun (λ a₁ → CPSApp
                            (CPSApp (CPSVal (cpsV (τ₆ ⇒ τ₄ cps[ τ₅ , τ₇ ]) v₁)) (CPSVal (CPSVar a₁)))
                            (CPSVal (CPSFun (λ a → κ (CPSVar a)))))))))
    (CPSFun (λ x → CPSVal (CPSFun (λ k → cpsI′ τ₆ τ₇ τ₂ (pcontext-plug τ₁ p₂′ (Val (Var x))) (CPSVar k)))))
  ≡⟨ refl ⟩
    cpsI τ₁ τ₂ τ₃ (Shift α τ τ₃ τ₁ τ₂ e₁)
      (λ n₁ → CPSApp
                (CPSApp
                   (CPSVal (CPSFun (λ x → CPSVal (CPSFun (λ k →
                             cpsI′ τ₆ τ₇ τ₂ (pcontext-plug τ₁ p₂′ (Val (Var x))) (CPSVar k))))))
                   (CPSVal n₁))
                (CPSVal (CPSFun (λ a₁ → CPSApp (CPSApp (CPSVal (cpsV (τ₆ ⇒ τ₄ cps[ τ₅ , τ₇ ]) v₁)) (CPSVal (CPSVar a₁)))
                                                (CPSVal (CPSFun (λ a → κ (CPSVar a))))))))
  ≡⟨ refl ⟩
    CPSLet (CPSVal (CPSFun λ a → CPSVal (CPSFun (λ κ′ →
               CPSApp (CPSVal (CPSVar κ′))
                      (CPSApp (CPSApp (CPSVal (CPSFun (λ x → CPSVal (CPSFun (λ k →
                                         cpsI′ τ₆ τ₇ τ₂ (pcontext-plug τ₁ p₂′ (Val (Var x))) (CPSVar k))))))
                                      (CPSVal (CPSVar a)))
                              (CPSVal (CPSFun (λ a₁ → CPSApp (CPSApp (CPSVal (cpsV (τ₆ ⇒ τ₄ cps[ τ₅ , τ₇ ]) v₁)) (CPSVal (CPSVar a₁)))
                                                             (CPSVal (CPSFun (λ a₂ → κ (CPSVar a₂))))))))))))
           (λ c → cpsI τ τ τ₃ (e₁ c) (λ m → CPSVal m))
  ⟶⟨ eqLet₁ (λ c₁ → cpsI τ τ τ₃ (e₁ c₁) (λ m → CPSVal m))
             (eqFun (λ a → eqFun (λ κ′ → eqApp₂ (eqApp₁ (eqBeta (sVal (sFun (λ x →
               ekSubst′ x (subst-context p₂′ (Var a)))))))))) ⟩
    CPSLet (CPSVal (CPSFun (λ a → CPSVal (CPSFun (λ κ′ →
               CPSApp (CPSVal (CPSVar κ′))
                      (CPSApp
                        (CPSVal (CPSFun (λ k → cpsI′ τ₆ τ₇ τ₂ (pcontext-plug τ₁ p₂′ (Val (Var a))) (CPSVar k))))
                        (CPSVal (CPSFun (λ a₁ → CPSApp (CPSApp (CPSVal (cpsV (τ₆ ⇒ τ₄ cps[ τ₅ , τ₇ ]) v₁)) (CPSVal (CPSVar a₁)))
                                                        (CPSVal (CPSFun (λ a₂ → κ (CPSVar a₂)))))))))))))
           (λ c → cpsI τ τ τ₃ (e₁ c) (λ m → CPSVal m))
  ⟶⟨ eqLet₁ (λ c₁ → cpsI τ τ τ₃ (e₁ c₁) (λ m → CPSVal m))
             (eqFun (λ a → eqFun (λ κ′ → eqApp₂ (eqBeta (kSubst′ (pcontext-plug τ₁ p₂′ (Val (Var a)))))))) ⟩
    CPSLet (CPSVal (CPSFun (λ a → CPSVal (CPSFun (λ κ′ →
               CPSApp (CPSVal (CPSVar κ′))
                      (cpsI′ τ₆ τ₇ τ₂ (pcontext-plug τ₁ p₂′ (Val (Var a)))
                             (CPSFun (λ a₁ → CPSApp (CPSApp (CPSVal (cpsV (τ₆ ⇒ τ₄ cps[ τ₅ , τ₇ ]) v₁)) (CPSVal (CPSVar a₁)))
                                                     (CPSVal (CPSFun (λ a₂ → κ (CPSVar a₂))))))))))))
           (λ c → cpsI τ τ τ₃ (e₁ c) (λ m → CPSVal m))
  ≡⟨ refl ⟩
    CPSLet (CPSVal (CPSFun (λ a → CPSVal (CPSFun (λ κ′ →
               CPSApp (CPSVal (CPSVar κ′))
                      (cpsI′ τ₆ τ₇ τ₂ (pcontext-plug τ₁ p₂′ (Val (Var a)))
                             (CPSFun λ a₁ →
                               (λ y → CPSApp (CPSApp (CPSVal (cpsV (τ₆ ⇒ τ₄ cps[ τ₅ , τ₇ ]) v₁)) (CPSVal y))
                                              (CPSVal (CPSFun (λ a₂ → κ (CPSVar a₂)))))
                               (CPSVar a₁))))))))
           (λ c → cpsI τ τ τ₃ (e₁ c) (λ m → CPSVal m))
  ⟶⟨ eqLet₁ (λ c₁ → cpsI τ τ τ₃ (e₁ c₁) (λ m → CPSVal m))
              (eqFun (λ a → eqFun (λ κ′ → eqApp₂
              (cpsEtaEta′ (pcontext-plug τ₁ p₂′ (Val (Var a)))
                          (λ y → CPSApp (CPSApp (CPSVal (cpsV (τ₆ ⇒ τ₄ cps[ τ₅ , τ₇ ]) v₁)) (CPSVal y))
                                                 (CPSVal (CPSFun (λ a₂ → κ (CPSVar a₂)))))
                          λ v → sApp (sApp Subst≠ (sVal sVar=)) Subst≠)))) ⟩
    CPSLet (CPSVal (CPSFun (λ a → CPSVal (CPSFun (λ κ′ →
               CPSApp (CPSVal (CPSVar κ′))
                      (cpsI τ₆ τ₇ τ₂ (pcontext-plug τ₁ p₂′ (Val (Var a)))
                            (λ y → CPSApp (CPSApp (CPSVal (cpsV (τ₆ ⇒ τ₄ cps[ τ₅ , τ₇ ]) v₁)) (CPSVal y))
                                           (CPSVal (CPSFun (λ a₂ → κ (CPSVar a₂)))))))))))
           (λ c → cpsI τ τ τ₃ (e₁ c) (λ m → CPSVal m))
  ≡⟨ refl ⟩
    CPSLet (CPSVal (CPSFun (λ a → CPSVal (CPSFun (λ κ′ →
             CPSApp (CPSVal (CPSVar κ′))
                    (cpsI τ₆ τ₇ τ₂ (pcontext-plug τ₁ p₂′ (Val (Var a)))
                          (λ n₁ → CPSApp (CPSApp (CPSVal (cpsV (τ₆ ⇒ τ₄ cps[ τ₅ , τ₇ ]) v₁)) (CPSVal n₁)) (CPSVal (CPSFun (λ a₂ → κ (CPSVar a₂)))))))))))
           (λ c → cpsI τ τ τ₃ (e₁ c) (λ m → CPSVal m))
  ⟵⟨ eqLet₁ (λ c₁ → cpsI τ τ τ₃ (e₁ c₁) (λ m → CPSVal m))
             (eqFun (λ a → eqFun (λ κ′ → eqApp₂ (eqBeta
             (κSubst (pcontext-plug τ₁ p₂′ (Val (Var a)))
                      (λ k n₁ → CPSApp (CPSApp (CPSVal (cpsV (τ₆ ⇒ τ₄ cps[ τ₅ , τ₇ ]) v₁)) (CPSVal n₁)) (CPSVal k))
                      λ x → sApp Subst≠ (sVal sVar=)))))) ⟩
    CPSLet (CPSVal (CPSFun (λ a → CPSVal (CPSFun (λ κ′ →
             CPSApp (CPSVal (CPSVar κ′))
                    (CPSApp
                        (CPSVal (CPSFun (λ k →
                          cpsI τ₆ τ₇ τ₂ (pcontext-plug τ₁ p₂′ (Val (Var a)))
                               (λ n₁ → CPSApp (CPSApp (CPSVal (cpsV (τ₆ ⇒ τ₄ cps[ τ₅ , τ₇ ]) v₁)) (CPSVal n₁))
                                               (CPSVal (CPSVar k))))))
                      (CPSVal (CPSFun (λ a₂ → κ (CPSVar a₂))))))))))
           (λ c → cpsI τ τ τ₃ (e₁ c) (λ m → CPSVal m))
  ⟵⟨ eqLet₁ (λ c₁ → cpsI τ τ τ₃ (e₁ c₁) (λ m → CPSVal m))
             (eqFun (λ a → eqFun (λ κ′ → eqApp₂ (eqApp₁ (eqBeta (sVal (sFun (λ x →
             eSubst (subst-context p₂′ (Var a))
                    λ x₁ → sApp (sApp Subst≠ (sVal x₁)) Subst≠)))))))) ⟩
    CPSLet (CPSVal (CPSFun (λ a → CPSVal (CPSFun (λ κ′ →
             CPSApp (CPSVal (CPSVar κ′))
                    (CPSApp
                        (CPSApp (CPSVal (CPSFun (λ x → CPSVal (CPSFun (λ k →
                                   cpsI τ₆ τ₇ τ₂ (pcontext-plug τ₁ p₂′ (Val (Var x)))
                                        (λ n₁ → CPSApp (CPSApp (CPSVal (cpsV (τ₆ ⇒ τ₄ cps[ τ₅ , τ₇ ]) v₁)) (CPSVal n₁))
                                                        (CPSVal (CPSVar k))))))))
                              (CPSVal (CPSVar a)))
                      (CPSVal (CPSFun (λ a₂ → κ (CPSVar a₂))))))))))
           (λ c → cpsI τ τ τ₃ (e₁ c) (λ m → CPSVal m))
  ≡⟨ refl ⟩
    (λ m → cpsI τ₁ τ₂ τ₃ (Shift α τ τ₃ τ₁ τ₂ e₁)
                 (λ n → CPSApp (CPSApp (CPSVal m) (CPSVal n)) (CPSVal (CPSFun (λ a → κ (CPSVar a))))))
    (CPSFun (λ x → CPSVal (CPSFun (λ k → cpsI τ₆ τ₇ τ₂ (pcontext-plug τ₁ p₂′ (Val (Var x)))
                                               (λ n₁ → CPSApp (CPSApp (CPSVal (cpsV (τ₆ ⇒ τ₄ cps[ τ₅ , τ₇ ]) v₁)) (CPSVal n₁)) (CPSVal (CPSVar k)))))))
  ≡⟨ refl ⟩
    (λ m → cpsI τ₁ τ₂ τ₃ (Shift α τ τ₃ τ₁ τ₂ e₁)
                 (λ n → CPSApp (CPSApp (CPSVal m) (CPSVal n)) (CPSVal (CPSFun (λ a → κ (CPSVar a))))))
    (CPSFun (λ x → CPSVal (CPSFun (λ k → cpsI′ τ₄ τ₅ τ₂ (App (Val v₁) (pcontext-plug τ₁ p₂′ (Val (Var x)))) (CPSVar k)))))
  ≡⟨ refl ⟩
    (λ m → cpsI τ₁ τ₂ τ₃ (Shift α τ τ₃ τ₁ τ₂ e₁)
                 (λ n → CPSApp (CPSApp (CPSVal m) (CPSVal n)) (CPSVal (CPSFun (λ a → κ (CPSVar a))))))
    (CPSFun (λ x → CPSVal (CPSFun (λ k → cpsI′ τ₄ τ₅ τ₂ (pcontext-plug τ₁ (Frame (App₂ v₁) p₂′) (Val (Var x))) (CPSVar k)))))
  ≡⟨ refl ⟩
    cpsI (τ₁ ⇒ τ₄ cps[ τ₅ , τ₂ ]) τ₃ τ₃
         (Val (Fun τ₄ τ₁ (λ x → pcontext-plug τ₁ (Frame (App₂ v₁) p₂′) (Val (Var x)))))
         (λ m → cpsI τ₁ τ₂ τ₃
                     (Shift α τ τ₃ τ₁ τ₂ e₁)
                     (λ n → CPSApp (CPSApp (CPSVal m) (CPSVal n)) (CPSVal (CPSFun (λ a → κ (CPSVar a))))))
  ≡⟨ refl ⟩
    cpsI τ₄ τ₅ τ₃
      (App (Val (Fun τ₄ τ₁ (λ x → pcontext-plug τ₁ (Frame (App₂ v₁) p₂′) (Val (Var x)))))
           (Shift α τ τ₃ τ₁ τ₂ e₁))
      κ
  ∎
