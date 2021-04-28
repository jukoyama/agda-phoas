module ColonTrans where

open import DSterm
open import CPSterm

-- CPS transformation

open import Function

cpsT : typ → cpstyp
cpsT Nat = Nat
cpsT Boolean = Boolean
cpsT (τ₂ ⇒ τ₁ cps[ τ₃ , τ₄ ]) =
  cpsT τ₂ ⇒ ((cpsT τ₁ ⇒ cpsT τ₃) ⇒ cpsT τ₄)

-- CPS transformation to target term

mutual
  cpsV𝑐 : (τ₁ : typ) → {var : cpstyp → Set} →
          value[ var ∘ cpsT ] τ₁ cps[τ,τ] →
          cpsvalue𝑐[ var ] (cpsT τ₁)
  cpsV𝑐 .Nat (Num n) = CPSNum n
  cpsV𝑐 τ₁  (Var v) = CPSVar v
  cpsV𝑐 .(τ₂ ⇒ τ₁ cps[ τ₃ , τ₄ ]) (Fun τ₁ τ₂ {τ₃ = τ₃} {τ₄ = τ₄} e) =
    CPSFun (λ x → cpsEmain𝑐 τ₁ τ₃ τ₄ (e x))
  cpsV𝑐 .(((τ₃ ⇒ τ₄ cps[ τ , τ ]) ⇒ τ₁ cps[ τ₁ , τ₂ ]) ⇒ τ₃ cps[ τ₄ , τ₂ ])
        (Shift {τ = τ} {τ₁ = τ₁} {τ₂ = τ₂} {τ₃ = τ₃} {τ₄ = τ₄}) = CPSShift

  -- M : K
  cpsE𝑐 : (τ₁ τ₂ τ₃ : typ) → {var : cpstyp → Set} →
          term[ var ∘ cpsT ] τ₁ cps[ τ₂ , τ₃ ] →
          cpscont𝑐[ var ] (cpsT τ₁ ⇒ cpsT τ₂) →
          -- (cpsvalue𝑐[ var ] (cpsT τ₁) → cpsterm𝑐[ var ] (cpsT τ₂)) → 
          cpsterm𝑐[ var ] (cpsT τ₃)
  -- V : K
  cpsE𝑐 τ₁ τ₂ .τ₂ (Val v) κ = CPSRet κ (cpsV𝑐 τ₁ v)
  -- (PQ) : K
  cpsE𝑐 τ₁ τ₂ τ₃ (NonVal {τ₁ = .τ₁} {τ₂ = .τ₂} {τ₃ = .τ₃}
        (App {τ₁ = .τ₁} {τ₂ = τ₄} {τ₃ = .τ₂} {τ₄ = τ₅} {τ₅ = τ₆} {τ₆ = .τ₃}
        (NonVal {τ₁ = .(τ₄ ⇒ τ₁ cps[ τ₂ , τ₅ ])} {τ₂ = .τ₆} {τ₃ = .τ₃} e₁)
        (NonVal {τ₁ = .τ₄} {τ₂ = .τ₅} {τ₃ = .τ₆} e₂))) κ =
        cpsE𝑐 (τ₄ ⇒ τ₁ cps[ τ₂ , τ₅ ]) τ₆ τ₃ (NonVal e₁)
              (CPSCont (λ m →
                cpsE𝑐 τ₄ τ₅ τ₆ (NonVal e₂)
                      (CPSCont (λ n → CPSApp (CPSVar m) (CPSVar n) κ))))
  -- (PW) : K
  cpsE𝑐 τ₁ τ₂ τ₃ (NonVal {τ₁ = .τ₁} {τ₂ = .τ₂} {τ₃ = .τ₃}
        (App {τ₁ = .τ₁} {τ₂ = τ₄} {τ₃ = .τ₂} {τ₄ = τ₅} {τ₅ = .τ₅} {τ₆ = .τ₃}
        (NonVal {τ₁ = .(τ₄ ⇒ τ₁ cps[ τ₂ , τ₅ ])} {τ₂ = .τ₅} {τ₃ = .τ₃} e₁)
        (Val {τ₁ = .τ₄} {τ₂ = .τ₅} v₂))) κ =
        cpsE𝑐 (τ₄ ⇒ τ₁ cps[ τ₂ , τ₅ ]) τ₅ τ₃ (NonVal e₁)
              (CPSCont (λ m → CPSApp (CPSVar m) (cpsV𝑐 τ₄ v₂) κ))
  -- (VQ) : K
  cpsE𝑐 τ₁ τ₂ τ₃ (NonVal {τ₁ = .τ₁} {τ₂ = .τ₂} {τ₃ = .τ₃}
        (App {τ₁ = .τ₁} {τ₂ = τ₄} {τ₃ = .τ₂} {τ₄ = τ₅} {τ₅ = .τ₃} {τ₆ = .τ₃}
        (Val {τ₁ = .(τ₄ ⇒ τ₁ cps[ τ₂ , τ₅ ])} {τ₂ = .τ₃} v₁)
        (NonVal {τ₁ = .τ₄} {τ₂ = .τ₅} {τ₃ = .τ₃} e₂))) κ =
        cpsE𝑐 τ₄ τ₅ τ₃ (NonVal e₂)
              (CPSCont (λ n → CPSApp (cpsV𝑐 (τ₄ ⇒ τ₁ cps[ τ₂ , τ₅ ]) v₁) (CPSVar n) κ))
  -- (VW) : K
  cpsE𝑐 τ₁ τ₂ τ₃ (NonVal {τ₁ = .τ₁} {τ₂ = .τ₂} {τ₃ = .τ₃}
        (App {τ₁ = .τ₁} {τ₂ = τ₄} {τ₃ = .τ₂} {τ₄ = .τ₃} {τ₅ = .τ₃} {τ₆ = .τ₃}
        (Val {τ₁ = .(τ₄ ⇒ τ₁ cps[ τ₂ , τ₃ ])} {τ₂ = .τ₃} v₁)
        (Val {τ₁ = .τ₄} {τ₂ = .τ₃} v₂))) κ =
        CPSApp (cpsV𝑐 (τ₄ ⇒ τ₁ cps[ τ₂ , τ₃ ]) v₁) (cpsV𝑐 τ₄ v₂) κ
  -- ⟨ M ⟩ : K
  cpsE𝑐 τ₁ τ₂ .τ₂ (NonVal {τ₁ = .τ₁} {τ₂ = .τ₂} {τ₃ = .τ₂}
        (Reset τ₃ .τ₁ .τ₂ e)) κ = CPSRetE κ (cpsE𝑐 τ₃ τ₃ τ₁ e (CPSId (λ x → CPSVar x)))
  -- (let x = M in N) : K   
  cpsE𝑐 τ₁ τ₂ τ₃ (NonVal {τ₁ = .τ₁} {τ₂ = .τ₂} {τ₃ = .τ₃}
        (Let {τ₁ = τ₄} {τ₂ = .τ₁} {α = .τ₂} {β = β} {γ = .τ₃} e₁ e₂)) κ =
        cpsE𝑐 τ₄ β τ₃ e₁ (CPSCont (λ c → cpsE𝑐 τ₁ τ₂ β (e₂ c) κ))

  -- M*
  cpsEmain𝑐 : (τ₁ τ₂ τ₃ : typ) → {var : cpstyp → Set} →
         term[ var ∘ cpsT ] τ₁ cps[ τ₂ , τ₃ ] →
         cpsroot𝑐[ var ] ((cpsT τ₁ ⇒ cpsT τ₂) ⇒ cpsT τ₃)
  cpsEmain𝑐 τ₁ τ₂ τ₃ e = CPSRoot (λ k → cpsE𝑐 τ₁ τ₂ τ₃ e (CPSKVar k)) 
