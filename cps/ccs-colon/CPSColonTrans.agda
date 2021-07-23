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
             (cvar (cpsT τ₂) (cpsT τ₁ ⇒ cpsT τ₂) → cpsterm𝑐[ var , cvar ] (cpsT τ₁ ⇒ cpsT τ₂) (cpsT τ₃))
  cpsMain𝑐 τ₁ τ₂ τ₃ e = λ k → cpsE𝑐 τ₁ τ₂ τ₃ τ₁ τ₂ e (CPSKVar k)

  cpsV𝑐 : (τ₁ : typ) → {var : cpstyp → Set} {cvar : cpstyp → conttyp → Set} →
          value[ var ∘ cpsT ] τ₁ cps[τ,τ] →
          cpsvalue𝑐[ var , cvar ] (cpsT τ₁)
  cpsV𝑐 .Nat (Num n) = CPSNum n
  cpsV𝑐 τ₁  (Var v) = CPSVar v
  -- なぜ、τ₃ なのかわかっていない
  cpsV𝑐 .(τ₂ ⇒ τ₁ cps[ τ₃ , τ₄ ]) (Fun τ₁ τ₂ {τ₃ = τ₃} {τ₄ = τ₄} e) =
    CPSFun {τ = cpsT τ₃} (λ x k → cpsE𝑐 τ₁ τ₃ τ₄ τ₁ τ₃ (e x) (CPSKVar k))
  cpsV𝑐 .(((τ₃ ⇒ τ₄ cps[ τ , τ ]) ⇒ τ₁ cps[ τ₁ , τ₂ ]) ⇒ τ₃ cps[ τ₄ , τ₂ ])
        (Shift {τ = τ} {τ₁ = τ₁} {τ₂ = τ₂} {τ₃ = τ₃} {τ₄ = τ₄}) = CPSShift

  -- M : K
  cpsE𝑐 : (τ₁ τ₂ τ₃ τ₄ τ₅ : typ) → {var : cpstyp → Set} {cvar : cpstyp → conttyp → Set} →
          term[ var ∘ cpsT ] τ₁ cps[ τ₂ , τ₃ ] →
          cpscont𝑐[ var , cvar ] (cpsT τ₄ ⇒ cpsT τ₅) (cpsT τ₁ ⇒ cpsT τ₂) →
          cpsterm𝑐[ var , cvar ] (cpsT τ₄ ⇒ cpsT τ₅) (cpsT τ₃)
          
  -- V : K
  cpsE𝑐 τ₁ τ₂ .τ₂ τ₄ τ₅ (Val v) κ = CPSRet κ (cpsV𝑐 τ₁ v)

  -- (PQ) : K
  cpsE𝑐 τ₁ τ₂ τ₃ τ₄ τ₅ (NonVal {τ₁ = .τ₁} {τ₂ = .τ₂} {τ₃ = .τ₃}
        (App {τ₁ = .τ₁} {τ₂ = τ₆} {τ₃ = .τ₂} {τ₄ = τ₇} {τ₅ = τ₈} {τ₆ = .τ₃}
             (NonVal {τ₁ = .(τ₆ ⇒ τ₁ cps[ τ₂ , τ₇ ])} {τ₂ = .τ₈} {τ₃ = .τ₃} e₁)
             (NonVal {τ₁ = .τ₆} {τ₂ = .τ₇} {τ₃ = .τ₈} e₂))) κ =
    cpsE𝑐 (τ₆ ⇒ τ₁ cps[ τ₂ , τ₇ ]) τ₈ τ₃ τ₄ τ₅ (NonVal e₁)
          (CPSCont (λ m →
              cpsE𝑐 τ₆ τ₇ τ₈ τ₄ τ₅ (NonVal e₂)
                    (CPSCont (λ n → CPSApp (CPSVar m) (CPSVar n) κ))))

  -- (PW) : K
  cpsE𝑐 τ₁ τ₂ τ₃ τ₄ τ₅ (NonVal {τ₁ = .τ₁} {τ₂ = .τ₂} {τ₃ = .τ₃}
        (App {τ₁ = .τ₁} {τ₂ = τ₆} {τ₃ = .τ₂} {τ₄ = τ₇} {τ₅ = .τ₇} {τ₆ = .τ₃}
             (NonVal {τ₁ = .(τ₆ ⇒ τ₁ cps[ τ₂ , τ₇ ])} {τ₂ = .τ₇} {τ₃ = .τ₃} e₁)
             (Val {τ₁ = .τ₆} {τ₂ = .τ₇} v₂))) κ =
    cpsE𝑐 (τ₆ ⇒ τ₁ cps[ τ₂ , τ₇ ]) τ₇ τ₃ τ₄ τ₅ (NonVal e₁)
          (CPSCont (λ m → CPSApp (CPSVar m) (cpsV𝑐 τ₆ v₂) κ))
    
  -- (VQ) : K
  cpsE𝑐 τ₁ τ₂ τ₃ τ₄ τ₅ (NonVal {τ₁ = .τ₁} {τ₂ = .τ₂} {τ₃ = .τ₃}
        (App {τ₁ = .τ₁} {τ₂ = τ₆} {τ₃ = .τ₂} {τ₄ = τ₇} {τ₅ = .τ₃} {τ₆ = .τ₃}
             (Val {τ₁ = .(τ₆ ⇒ τ₁ cps[ τ₂ , τ₇ ])} {τ₂ = .τ₃} v₁)
             (NonVal {τ₁ = .τ₆} {τ₂ = .τ₇} {τ₃ = .τ₃} e₂))) κ =
    cpsE𝑐 τ₆ τ₇ τ₃ τ₄ τ₅ (NonVal e₂)
          (CPSCont (λ n → CPSApp (cpsV𝑐 (τ₆ ⇒ τ₁ cps[ τ₂ , τ₇ ]) v₁) (CPSVar n) κ))

  -- (VW): K
  cpsE𝑐 τ₁ τ₂ τ₃ τ₄ τ₅ (NonVal {τ₁ = .τ₁} {τ₂ = .τ₂} {τ₃ = .τ₃}
        (App {τ₁ = .τ₁} {τ₂ = τ₆} {τ₃ = .τ₂} {τ₄ = .τ₃} {τ₅ = .τ₃} {τ₆ = .τ₃}
             (Val {τ₁ = .(τ₆ ⇒ τ₁ cps[ τ₂ , τ₃ ])} {τ₂ = .τ₃} v₁)
             (Val {τ₁ = .τ₆} {τ₂ = .τ₃} v₂))) κ =
    CPSApp (cpsV𝑐 (τ₆ ⇒ τ₁ cps[ τ₂ , τ₃ ]) v₁) (cpsV𝑐 τ₆ v₂) κ

  -- ⟨ M ⟩ : K
  cpsE𝑐 τ₁ τ₂ .τ₂ τ₄ τ₅ (NonVal {τ₁ = .τ₁} {τ₂ = .τ₂} {τ₃ = .τ₂} (Reset τ₃ .τ₁ .τ₂ e)) κ =
    CPSRetE κ (cpsE𝑐 τ₃ τ₃ τ₁ τ₃ τ₃ e CPSId)

  -- (let x = M in N) : K
  cpsE𝑐 τ₁ τ₂ τ₃ τ₄ τ₅ (NonVal (Let {τ₁ = τ₆} {τ₂ = .τ₁} {α = .τ₂} {β = β} {γ = .τ₃} e₁ e₂)) κ =
    cpsE𝑐 τ₆ β τ₃ τ₄ τ₅ e₁ (CPSCont (λ c → cpsE𝑐 τ₁ τ₂ β τ₄ τ₅ (e₂ c) κ))
