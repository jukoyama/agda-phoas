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
cpsT (τ₂ ▷ τ₁) = cpsT τ₂ ⇒ cpsT τ₁

-- CPS transformation to target term

mutual
  cpsV𝑐 : {var : cpstyp → Set} → {τ₁ : typ} →
          value[ var ∘ cpsT ] τ₁ cps[τ,τ] →
          cpsvalue𝑐[ var ] (cpsT τ₁)
  cpsV𝑐 (Num n) = CPSNum n
  cpsV𝑐 (Var x) = CPSVar x
  cpsV𝑐 (Fun e) = CPSFun (λ x k → cpsE𝑐 (e x) (CPSKVar k))
  cpsV𝑐 Shift = CPSShift

  -- M : K
  cpsE𝑐 : {var : cpstyp → Set} → {τ₁ τ₂ τ₃ : typ} →
          term[ var ∘ cpsT ] τ₁ cps[ τ₂ , τ₃ ] →
          cpscont𝑐[ var ] cpsT τ₁ ⇒ cpsT τ₂ →
          cpsterm𝑐[ var ] (cpsT τ₃)

  -- V : K
  cpsE𝑐 (Val v) k = CPSRet k (cpsV𝑐 v)

  -- P Q : K
  cpsE𝑐 (NonVal (App (NonVal e₁) (NonVal e₂))) k =
    cpsE𝑐 (NonVal e₁) (CPSCont (λ m →
      cpsE𝑐 (NonVal e₂) (CPSCont (λ n →
        CPSApp (CPSVar m) (CPSVar n) k))))

  -- P W : K
  cpsE𝑐 (NonVal (App (NonVal e₁) (Val v₂))) k =
    cpsE𝑐 (NonVal e₁) (CPSCont (λ m →
      CPSApp (CPSVar m) (cpsV𝑐 v₂) k))

  -- V Q : K
  cpsE𝑐 (NonVal (App (Val v₁) (NonVal e₂))) k =
    cpsE𝑐 (NonVal e₂) (CPSCont (λ n →
      CPSApp (cpsV𝑐 v₁) (CPSVar n) k))

  -- V W : K
  cpsE𝑐 (NonVal (App (Val v₁) (Val v₂))) k =
    CPSApp (cpsV𝑐 v₁) (cpsV𝑐 v₂) k

  -- ⟨ M ⟩ : K
  cpsE𝑐 (NonVal (Reset e)) k =
    CPSRetE k (cpsE𝑐 e CPSId)

  cpsE𝑐 (NonVal (Let e₁ e₂)) k =
    cpsE𝑐 e₁ (CPSCont (λ m →
      cpsE𝑐 (e₂ m) k))
