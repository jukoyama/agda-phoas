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

cpsT𝑘𝑐 : typ𝑘𝑐 → conttyp
cpsT𝑘𝑐 (τ₂ ▷ τ₁) = cpsT𝑘 τ₂ ⇒ cpsT𝑘 τ₁

-- CPS transforamtion to target term

mutual
  cpsV𝑘 : {var : cpstyp → Set} {cvar : conttyp → Set} → {τ₁ : typ𝑘} →
          value𝑘[ var ∘ cpsT𝑘 , cvar ∘ cpsT𝑘𝑐 ] τ₁ cps[τ,τ] →
          cpsvalue𝑐[ var , cvar ] (cpsT𝑘 τ₁)
  cpsV𝑘 (Num n) = CPSNum n
  cpsV𝑘 (Var x) = CPSVar x
  cpsV𝑘 (Fun e) = CPSFun (λ x k → cpsE𝑘 (e x k))
  cpsV𝑘 Shift = CPSShift

  cpsE𝑘 : {var : cpstyp → Set} {cvar : conttyp → Set} → {τ : typ𝑘} →
          term𝑘[ var ∘ cpsT𝑘 , cvar ∘ cpsT𝑘𝑐 ] τ →
          cpsterm𝑐[ var , cvar ] (cpsT𝑘 τ)
  cpsE𝑘 (Ret k v) = CPSRet (cpsC𝑘 k) (cpsV𝑘 v)
  cpsE𝑘 (App v w k) = CPSApp (cpsV𝑘 v) (cpsV𝑘 w) (cpsC𝑘 k)
  cpsE𝑘 (RetE k e) = CPSRetE (cpsC𝑘 k) (cpsE𝑘 e)

  cpsC𝑘 : {var : cpstyp → Set} {cvar : conttyp → Set} → {τ₁ τ₂ : typ𝑘} →
          pcontext𝑘[ var ∘ cpsT𝑘 , cvar ∘ cpsT𝑘𝑐 ] (τ₁ ▷ τ₂) →
          cpscont𝑐[ var , cvar ] (cpsT𝑘 τ₁ ⇒ cpsT𝑘 τ₂)
  cpsC𝑘 (KHole k) = CPSKVar k
  cpsC𝑘 Hole = CPSId
  cpsC𝑘 (KLet e) = CPSCont (λ x → cpsE𝑘 (e x))
