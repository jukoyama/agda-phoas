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
  cpsMain𝑘 : {var : cpstyp → Set} → (τ τ₁ τ₂ τ₃ τ₄ : typ𝑘) →
             ((var ∘ cpsT𝑘) (τ₁ ⇒ τ₃ cps[ τ , τ ]) →
               term𝑘[ var ∘ cpsT𝑘 ] τ₂ cps[ τ₂ , τ₄ ]) →
             (var (cpsT𝑘 τ₁ ⇒[ cpsT𝑘 τ₃ ⇒ cpsT𝑘 τ ]⇒ cpsT𝑘 τ) →
               cpsterm𝑐[ var ] (cpsT𝑘 τ₂ ⇒ cpsT𝑘 τ₂) (cpsT𝑘 τ₄))
  cpsMain𝑘 τ τ₁ τ₂ τ₃ τ₄ r = λ k → cpsE𝑘 τ₄ τ₂ (r k)
  -- cpsMain𝑘 τ₁ τ₂ τ₃ (Root e) = λ k → cpsE𝑘 τ₃ τ₂ (e k)
  
  cpsV𝑘 : {var : cpstyp → Set} → (τ₁ : typ𝑘) →
          value𝑘[ var ∘ cpsT𝑘 ] τ₁ cps[τ,τ] →
          cpsvalue𝑐[ var ] (cpsT𝑘 τ₁)
  cpsV𝑘 .Nat (Num n) = CPSNum n
  cpsV𝑘 τ₁ (Var {τ₁ = .τ₁} v) = CPSVar v
  cpsV𝑘 .(τ₀ ⇒ τ₁ cps[ τ₃ , τ₄ ]) (Fun τ₀ τ τ₁ τ₂ {τ₃ = τ₃} {τ₄ = τ₄} e) =
    CPSFun (λ x → cpsMain𝑘 τ τ₁ τ₂ τ₃ τ₄ (e x))
  cpsV𝑘 {var} .(((τ₃ ⇒ τ₄ cps[ τ , τ ]) ⇒ τ₁ cps[ τ₁ , τ₂ ]) ⇒ τ₃ cps[ τ₄ , τ₂ ])
              (Shift {τ = τ} {τ₁ = τ₁} {τ₂ = τ₂} {τ₃ = τ₃} {τ₄ = τ₄}) = CPSShift
  
  cpsC𝑘 : {var : cpstyp → Set} → (τ₁ τ₂ τ₃ τ₅ : typ𝑘) →
          pcontext𝑘[ var ∘ cpsT𝑘 , τ₁ cps[ τ₂ , τ₃ ]] τ₅ cps[ τ₅ , τ₃ ] → 
          cpscont𝑐[ var ] (cpsT𝑘 τ₅ ⇒ cpsT𝑘 τ₅) (cpsT𝑘 τ₃) (cpsT𝑘 τ₁ ⇒ cpsT𝑘 τ₂)
  cpsC𝑘 τ₁ τ₂ τ₃ .τ₂  (KHole {τ₁ = .τ₁} {τ₂ = .τ₂} {τ₃ = .τ₃} k) = CPSKVar k
  cpsC𝑘 τ₁ .τ₁ τ₃ .τ₁ (Hole {τ₁ = .τ₁} {τ₃ = .τ₃}) = CPSId
  cpsC𝑘 τ₁ τ₂ τ₃ τ₅   (KLet {τ₁ = .τ₁} {τ₂ = .τ₅} {β = .τ₂} {γ = .τ₃} e₂) =
    CPSCont (λ x → cpsE𝑘 τ₂ τ₅ (e₂ x))

  cpsE𝑘 : {var : cpstyp → Set} → (τ₃ τ₅ : typ𝑘) → 
          term𝑘[ var ∘ cpsT𝑘 ] τ₅ cps[ τ₅ , τ₃ ] →
          cpsterm𝑐[ var ] (cpsT𝑘 τ₅ ⇒ cpsT𝑘 τ₅) (cpsT𝑘 τ₃)
  cpsE𝑘 τ₃ τ₅ (Val {τ₁ = τ₁} {τ₂ = .τ₃} {τ₄ = .τ₅} k v) =
    CPSRet (cpsC𝑘 τ₁ τ₃ τ₃ τ₅ k) (cpsV𝑘 τ₁ v)
  cpsE𝑘 τ₃ τ₅ (NonVal {τ₁ = τ₁} {τ₂ = τ₂} {τ₃ = .τ₃} {τ₄ = .τ₅} k
        (App {τ₁ = .τ₁} {τ₂ = τ₄} {τ₃ = .τ₂} {τ₄ = .τ₃} v w)) =
    CPSApp (cpsV𝑘 (τ₄ ⇒ τ₁ cps[ τ₂ , τ₃ ]) v) (cpsV𝑘 τ₄ w) (cpsC𝑘 τ₁ τ₂ τ₃ τ₅ k)
  cpsE𝑘 τ₃ τ₅ (NonVal {τ₁ = τ₁} {τ₂ = .τ₃} {τ₃ = .τ₃} {τ₄ = .τ₅} k (Reset τ₂ .τ₁ .τ₃ e)) =
    CPSRetE (cpsC𝑘 τ₁ τ₃ τ₃ τ₅ k) (cpsE𝑘 τ₁ τ₂ e)
  
