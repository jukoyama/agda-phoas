module CPSColonTrans where

open import DSterm
open import CPSterm

-- CPS transformation

open import Function

cpsT : typ → cpstyp
cpsT Nat     = Nat
cpsT Boolean = Boolean
cpsT (τ₂ ⇒ τ₁ cps[ τ₃ , τ₄ ]) =
  cpsT τ₂ ⇒[ cpsT τ₁ ⇒ cpsT τ₃ ]⇒ cpsT τ₄

-- CPS transformation to target term

mutual
  cpsMain𝑐 : (τ₁ τ₂ τ₃ : typ) → {var : cpstyp → Set} {cvar : cpstyp → conttyp → Set} →
             term[ var ∘ cpsT ] τ₁ cps[ τ₂ , τ₃ ] →
             (cvar (cpsT τ₂) (cpsT τ₁ ⇒ cpsT τ₂) → cpsterm𝑐[ var , cvar ] (cpsT τ₂ ⇒ cpsT τ₂) (cpsT τ₃))
  cpsMain𝑐 τ₁ τ₂ τ₃ e = λ k → cpsE𝑐 τ₁ τ₂ τ₃ τ₂ e (CPSKVar k)

  cpsV𝑐 : (τ₁ : typ) → {var : cpstyp → Set} {cvar : cpstyp → conttyp → Set} →
          value[ var ∘ cpsT ] τ₁ cps[τ,τ] →
          cpsvalue𝑐[ var , cvar ] (cpsT τ₁)
  cpsV𝑐 .Nat (Num n) = CPSNum n
  cpsV𝑐 τ₁  (Var v) = CPSVar v
  cpsV𝑐 .(τ₂ ⇒ τ₁ cps[ τ₃ , τ₄ ]) (Fun τ₁ τ₂ {τ₃ = τ₃} {τ₄ = τ₄} e) =
    CPSFun (λ x → cpsMain𝑐 τ₁ τ₃ τ₄ (e x))
    -- CPSFun {τ = cpsT τ₃} (λ x k → cpsE𝑐 τ₁ τ₃ τ₄ τ₃ (e x) (CPSKVar k))
  cpsV𝑐 .(((τ₃ ⇒ τ₄ cps[ τ , τ ]) ⇒ τ₁ cps[ τ₁ , τ₂ ]) ⇒ τ₃ cps[ τ₄ , τ₂ ])
        (Shift {τ = τ} {τ₁ = τ₁} {τ₂ = τ₂} {τ₃ = τ₃} {τ₄ = τ₄}) = CPSShift

  -- M : K
  cpsE𝑐 : (τ₁ τ₂ τ₃ τ₄ : typ) → {var : cpstyp → Set} {cvar : cpstyp → conttyp → Set} →
          term[ var ∘ cpsT ] τ₁ cps[ τ₂ , τ₃ ] →
          cpscont𝑐[ var , cvar ] (cpsT τ₄ ⇒ cpsT τ₄) (cpsT τ₁ ⇒ cpsT τ₂) →
          cpsterm𝑐[ var , cvar ] (cpsT τ₄ ⇒ cpsT τ₄) (cpsT τ₃)

  -- V : K
  cpsE𝑐 τ₁ τ₂ .τ₂ τ₄ (Val {τ₁ = .τ₁} {τ₂ = .τ₂} v) κ = CPSRet κ (cpsV𝑐 τ₁ v)

  -- P Q : K
  cpsE𝑐 τ₁ τ₂ τ₃ τ₄
        (NonVal {τ₁ = .τ₁} {τ₂ = .τ₂} {τ₃ = .τ₃}
        (App {τ₁ = .τ₁} {τ₂ = τ₅} {τ₃ = .τ₂} {τ₄ = τ₆} {τ₅ = τ₇} {τ₆ = .τ₃}
             (NonVal {τ₁ = .(τ₅ ⇒ τ₁ cps[ τ₂ , τ₆ ])} {τ₂ = .τ₇} {τ₃ = .τ₃} e₁)
             (NonVal {τ₁ = .τ₅} {τ₂ = .τ₆} {τ₃ = .τ₇} e₂))) κ =
    cpsE𝑐 (τ₅ ⇒ τ₁ cps[ τ₂ , τ₆ ]) τ₇ τ₃ τ₄ (NonVal e₁)
          (CPSCont (λ m →
    cpsE𝑐 τ₅ τ₆ τ₇ τ₄ (NonVal e₂)
          (CPSCont (λ n → CPSApp (CPSVar m) (CPSVar n) κ))))

  -- P W : K
  cpsE𝑐 τ₁ τ₂ τ₃ τ₄ (NonVal {τ₁ = .τ₁} {τ₂ = .τ₂} {τ₃ = .τ₃}
        (App {τ₁ = .τ₁} {τ₂ = τ₅} {τ₃ = .τ₂} {τ₄ = τ₆} {τ₅ = .τ₆} {τ₆ = .τ₃}
             (NonVal {τ₁ = .(τ₅ ⇒ τ₁ cps[ τ₂ , τ₆ ])} {τ₂ = .τ₆} {τ₃ = .τ₃} e₁)
             (Val {τ₁ = .τ₅} {τ₂ = .τ₆} v₂))) κ =
    cpsE𝑐 (τ₅ ⇒ τ₁ cps[ τ₂ , τ₆ ]) τ₆ τ₃ τ₄ (NonVal e₁)
          (CPSCont (λ m → CPSApp (CPSVar m) (cpsV𝑐 τ₅ v₂) κ))

  -- V Q : K
  cpsE𝑐 τ₁ τ₂ τ₃ τ₄ (NonVal {τ₁ = .τ₁} {τ₂ = .τ₂} {τ₃ = .τ₃}
        (App {τ₁ = .τ₁} {τ₂ = τ₅} {τ₃ = .τ₂} {τ₄ = τ₆} {τ₅ = .τ₃} {τ₆ = .τ₃}
             (Val {τ₁ = .(τ₅ ⇒ τ₁ cps[ τ₂ , τ₆ ])} {τ₂ = .τ₃} v₁)
             (NonVal {τ₁ = .τ₅} {τ₂ = .τ₆} {τ₃ = .τ₃} e₂))) κ =
    cpsE𝑐 τ₅ τ₆ τ₃ τ₄ (NonVal e₂)
          (CPSCont (λ n → CPSApp (cpsV𝑐 (τ₅ ⇒ τ₁ cps[ τ₂ , τ₆ ]) v₁) (CPSVar n) κ))

  -- V W : K
  cpsE𝑐 τ₁ τ₂ τ₃ τ₄
        (NonVal {τ₁ = .τ₁} {τ₂ = .τ₂} {τ₃ = .τ₃}
        (App {τ₁ = .τ₁} {τ₂ = τ₅} {τ₃ = .τ₂} {τ₄ = .τ₃} {τ₅ = .τ₃} {τ₆ = .τ₃}
             (Val {τ₁ = .(τ₅ ⇒ τ₁ cps[ τ₂ , τ₃ ])} {τ₂ = .τ₃} v₁)
             (Val {τ₁ = .τ₅} {τ₂ = .τ₃} v₂))) κ =
    CPSApp (cpsV𝑐 (τ₅ ⇒ τ₁ cps[ τ₂ , τ₃ ]) v₁) (cpsV𝑐 τ₅ v₂) κ

  -- ⟨ M ⟩ : K
  cpsE𝑐 τ₁ τ₂ .τ₂ τ₄ (NonVal {τ₁ = .τ₁} {τ₂ = .τ₂} {τ₃ = .τ₂} (Reset τ₃ .τ₁ .τ₂ e)) κ =
    CPSRetE κ (cpsE𝑐 τ₃ τ₃ τ₁ τ₃ e CPSId)

  -- (let x = M in N) : K
  cpsE𝑐 τ₁ τ₂ τ₃ τ₄ (NonVal {τ₁ = .τ₁} {τ₂ = .τ₂} {τ₃ = .τ₃}
        (Let {τ₁ = τ₅} {τ₂ = .τ₁} {α = .τ₂} {β = β} {γ = .τ₃} e₁ e₂)) κ =
    cpsE𝑐 τ₅ β τ₃ τ₄ e₁
          (CPSCont (λ m → cpsE𝑐 τ₁ τ₂ β τ₄ (e₂ m) κ))

