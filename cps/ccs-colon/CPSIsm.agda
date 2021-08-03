module CPSIsm where

open import DStermK
open import CPSterm

-- DSkernel to CPS transformation

open import Function

cpsT𝑘 : typ𝑘 → cpstyp
cpsT𝑘 Nat     = Nat
cpsT𝑘 Boolean = Boolean
cpsT𝑘 (τ₂ ⇒ τ₁ cps[ τ₃ , τ₄ ]) =
  cpsT𝑘 τ₂ ⇒[ cpsT𝑘 τ₁ ⇒ cpsT𝑘 τ₃ ]⇒ cpsT𝑘 τ₄
  
-- CPS transforamtion to target term

mutual
  cpsV𝑘 : {var : cpstyp → Set} → (τ₁ : typ𝑘) →
          value𝑘[ var ∘ cpsT𝑘 ] τ₁ cps[τ,τ] →
          cpsvalue𝑐[ var , (λ { τ (τ₁ ⇒ τ₂) → var (τ₁ ⇒[ (τ₂ ⇒ τ) ]⇒ τ)}) ] (cpsT𝑘 τ₁)
  cpsV𝑘 .Nat (Num n) = CPSNum n
  cpsV𝑘 τ₁  (Var v) = CPSVar v
  cpsV𝑘 .(τ₂ ⇒ τ₁ cps[ τ₃ , τ₄ ]) (Fun τ τ₁ τ₂ {τ₃ = τ₃} {τ₄ = τ₄} e) =
    CPSFun {τ = cpsT𝑘 τ} (λ x k → {!cpsE𝑘 ? ? ?!})
  cpsV𝑘 .(((τ₃ ⇒ τ₄ cps[ τ , τ ]) ⇒ τ₁ cps[ τ₁ , τ₂ ]) ⇒ τ₃ cps[ τ₄ , τ₂ ])
        (Shift {τ = τ} {τ₁ = τ₁} {τ₂ = τ₂} {τ₃ = τ₃} {τ₄ = τ₄}) = CPSShift
  
  cpsC𝑘 : {var : cpstyp → Set} → (τ₁ τ₂ τ₃ τ₅ : typ𝑘) →
          pcontext𝑘[ var ∘ cpsT𝑘 , τ₁ cps[ τ₂ , τ₃ ]] τ₅ cps[ τ₅ , τ₃ ] → 
          cpscont𝑐[ var , (λ { τ (τ𝑐 ⇒ τ𝑐′) → var (τ𝑐 ⇒[ (τ𝑐′ ⇒ τ) ]⇒ τ)}) ]
                    (cpsT𝑘 τ₅ ⇒ cpsT𝑘 τ₅) (cpsT𝑘 τ₁ ⇒ cpsT𝑘 τ₂)
          
  cpsC𝑘 τ₁ .τ₁ τ₃ .τ₁ (Hole {τ₁ = .τ₁} {τ₂ = .τ₁} {τ₃ = .τ₃}) = CPSId
  cpsC𝑘 τ₁ τ₂ τ₃ .τ₂ (Frame {τ = .τ₃} {τ₁ = .τ₁} {τ₂ = .τ₂} {τ₇ = .τ₂} {τ₈ = .τ₂}
        (App₂ {τ₁ = .τ₂} {τ₂ = .τ₁} {τ₃ = .τ₂} {τ₅ = .τ₃} k) h) =
    CPSKVar k
  cpsC𝑘 τ₁ τ₂ τ₃ τ₅ (Frame {τ = .τ₃} {τ₁ = .τ₁} {τ₂ = .τ₂} {τ₇ = .τ₅} {τ₈ = .τ₅}
        (Let {τ₁ = .τ₁} {τ₂ = .τ₅} {α = .τ₅} {β = .τ₂} {γ = .τ₃} e) h) =
    CPSCont λ x → {!cpsE𝑘 ? ? (e x)!}

  cpsE𝑘 : {var : cpstyp → Set} → (τ₃ τ₅ : typ𝑘) → 
          term𝑘[ var ∘ cpsT𝑘 ] τ₅ cps[ τ₅ , τ₃ ] →
          cpsterm𝑐[ var , {!!} ] (cpsT𝑘 τ₅ ⇒ cpsT𝑘 τ₅) (cpsT𝑘 τ₃)
  cpsE𝑘 {var} τ₃ τ₅ (Val {τ₁ = τ₁} {τ₂ = .τ₃} {τ₄ = .τ₅} k v) = CPSRet {!!} (cpsV𝑘 {!!} {!v!})
  cpsE𝑘 {var} τ₃ τ₅ (NonVal {τ₁ = τ₁} {τ₂ = τ₂} {τ₃ = .τ₃} {τ₄ = .τ₅} x x₁) = {!!}
  
  -- cpsE𝑘 τ₃ τ₅ (Val {τ₁ = τ₁} {τ₂ = .τ₃} {τ₄ = .τ₅} k v) = CPSRet (cpsC𝑘 τ₁ τ₃ τ₃ τ₅ k) (cpsV𝑘 τ₁ v)
  -- cpsE𝑘 τ₃ τ₅ (NonVal {τ₁ = τ₁} {τ₂ = τ₂} {τ₃ = .τ₃} {τ₄ = .τ₅} k
  --       (App {τ₁ = .τ₁} {τ₂ = τ₆} {τ₃ = .τ₂} {τ₄ = .τ₃} v₁ v₂)) =
  --   CPSApp (cpsV𝑘 (τ₆ ⇒ τ₁ cps[ τ₂ , τ₃ ]) v₁) (cpsV𝑘 τ₆ v₂) (cpsC𝑘 τ₁ τ₂ τ₃ τ₅ k)
  -- cpsE𝑘 τ₃ τ₅ (NonVal {τ₁ = τ₁} {τ₂ = .τ₃} {τ₃ = .τ₃} {τ₄ = .τ₅} k (Reset τ₂ .τ₁ .τ₃ e)) =
  --   CPSRetE (cpsC𝑘 τ₁ τ₃ τ₃ τ₅ k) (cpsE𝑘 τ₁ τ₂ e)
