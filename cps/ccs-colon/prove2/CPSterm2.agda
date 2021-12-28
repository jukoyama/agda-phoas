module CPSterm2 where

open import Data.Nat
open import Function

-- target type
mutual
  data cpstyp : Set where
    Nat : cpstyp
    Boolean : cpstyp
    _⇒[_]⇒_ : cpstyp → conttyp → cpstyp → cpstyp
    
  data conttyp : Set where
    _⇒_ : cpstyp → cpstyp → conttyp

-- characterizing the image of CPS transformation
mutual
  data cpscont𝑐[_] (var : cpstyp → Set) : conttyp → conttyp → Set where
    -- CPSKVar で τ₂ を τ にすると、DS変換の
    -- dsC𝑐 の CPSKVar のケースで τ が何かわからなくなる
    CPSKVar : {τ₁ τ₂ : cpstyp} →
              var (τ₁ ⇒[ (τ₂ ⇒ τ₂) ]⇒ τ₂) →
              cpscont𝑐[ var ] (τ₂ ⇒ τ₂) (τ₁ ⇒ τ₂)
    CPSId   : {τ₁ : cpstyp} → cpscont𝑐[ var ] (τ₁ ⇒ τ₁) (τ₁ ⇒ τ₁)
    CPSCont : {τ₁ τ₂ τ₄ : cpstyp} → (var τ₁ → cpsterm𝑐[ var ] (τ₄ ⇒ τ₄) τ₂) →
              cpscont𝑐[ var ] (τ₄ ⇒ τ₄) (τ₁ ⇒ τ₂)

  data cpsvalue𝑐[_] (var : cpstyp → Set) : cpstyp → Set where
    CPSVar : {τ₁ : cpstyp} → var τ₁ → cpsvalue𝑐[ var ] τ₁
    CPSNum : ℕ → cpsvalue𝑐[ var ] Nat
    -- CHECK : τ => τ₃ に変更 (良いのか分からない)
    CPSFun : {τ₁ τ₂ τ₃ τ₄ : cpstyp} →
             -- (var τ₂ → var (τ₁ ⇒[ (τ₃ ⇒ τ) ]⇒ τ) → cpsterm𝑐[ var ] (τ₃ ⇒ τ₃) τ₄) →
             (var τ₂ → var (τ₁ ⇒[ (τ₃ ⇒ τ₃) ]⇒ τ₃) → cpsterm𝑐[ var ] (τ₃ ⇒ τ₃) τ₄) →
             -- (var τ₂ → cpsterm𝑐[ var ] (τ₃ ⇒ τ₃) τ₄) → 
             cpsvalue𝑐[ var ] (τ₂ ⇒[ τ₁ ⇒ τ₃ ]⇒ τ₄)
    CPSShift : {τ₁ τ₂ τ₃ τ₄ τ₅ : cpstyp} →
               cpsvalue𝑐[ var ]
                 (((τ₁ ⇒[ τ₂ ⇒ τ₃ ]⇒ τ₃) ⇒[ τ₄ ⇒ τ₄ ]⇒ τ₅) ⇒[ τ₁ ⇒ τ₂ ]⇒ τ₅)

  data cpsterm𝑐[_] (var : cpstyp → Set) : conttyp → cpstyp → Set where
    CPSRet : {τ₁ τ₂ τ₃ : cpstyp} →
             cpscont𝑐[ var ] (τ₃ ⇒ τ₃) (τ₁ ⇒ τ₂) →
             cpsvalue𝑐[ var ] τ₁ →
             cpsterm𝑐[ var ] (τ₃ ⇒ τ₃) τ₂
    CPSApp : {τ₁ τ₂ τ₃ τ₄ τ₅ : cpstyp} →
             cpsvalue𝑐[ var ] (τ₂ ⇒[ τ₁ ⇒ τ₃ ]⇒ τ₄) →
             cpsvalue𝑐[ var ] τ₂ →
             cpscont𝑐[ var ] (τ₅ ⇒ τ₅) (τ₁ ⇒ τ₃) →
             cpsterm𝑐[ var ] (τ₅ ⇒ τ₅) τ₄
    CPSRetE : {τ₀ τ₁ τ₂ τ₃ : cpstyp} →
             cpscont𝑐[ var ] (τ₃ ⇒ τ₃) (τ₁ ⇒ τ₂) →
             cpsterm𝑐[ var ] (τ₀ ⇒ τ₀) τ₁ →
             cpsterm𝑐[ var ] (τ₃ ⇒ τ₃) τ₂

-- 値による代入規則
mutual
  data cpsSubstValV𝑐 {var : cpstyp → Set} : {τ τ₁ : cpstyp} →
                     (var τ → cpsvalue𝑐[ var ] τ₁) →
                     cpsvalue𝑐[ var ] τ →
                     cpsvalue𝑐[ var ] τ₁ → Set where
    sVar= : {τ : cpstyp} {v : cpsvalue𝑐[ var ] τ} →
            cpsSubstValV𝑐 (λ x → CPSVar x) v v
    sVar≠ : {τ τ₁ : cpstyp} {v : cpsvalue𝑐[ var ] τ} {x : var τ₁} →
            cpsSubstValV𝑐 (λ _ → CPSVar x) v (CPSVar x)
    sNum  : {τ : cpstyp} {v : cpsvalue𝑐[ var ] τ}  {n : ℕ} →
            cpsSubstValV𝑐 (λ _ → CPSNum n) v (CPSNum n)
    sShift : {τ τ₁ τ₂ τ₃ τ₄ τ₅ : cpstyp} {v : cpsvalue𝑐[ var ] τ} →
             cpsSubstValV𝑐 (λ _ → CPSShift {τ₁ = τ₁} {τ₂} {τ₃} {τ₄} {τ₅}) v CPSShift
    sFun  : {τ τ₁ τ₂ τ₃ τ₄ : cpstyp} →
            {e  : var τ →  var τ₂ → var (τ₁ ⇒[ (τ₃ ⇒ τ₃) ]⇒ τ₃) → cpsterm𝑐[ var ] (τ₃ ⇒ τ₃) τ₄} → 
            {v  : cpsvalue𝑐[ var ] τ} →
            {e′ : var τ₂ → var (τ₁ ⇒[ (τ₃ ⇒ τ₃) ]⇒ τ₃) → cpsterm𝑐[ var ] (τ₃ ⇒ τ₃) τ₄} → 
            ((x : var τ₂) → (k : var (τ₁ ⇒[ (τ₃ ⇒ τ₃) ]⇒ τ₃)) →
              cpsSubstV𝑐 (λ y → (e y) x k) v (e′ x k)) → 
            cpsSubstValV𝑐 (λ y → CPSFun (λ x k → (e y) x k)) v (CPSFun (λ x k → e′ x k))

  data cpsSubstV𝑐 {var : cpstyp → Set} : {τ₁ τ₂ τ₃ : cpstyp} →
                  (var τ₁ → cpsterm𝑐[ var ] (τ₃ ⇒ τ₃) τ₂) →
                  cpsvalue𝑐[ var ] τ₁ →
                  cpsterm𝑐[ var ] (τ₃ ⇒ τ₃) τ₂ → Set where
    sApp  : {τ τ₁ τ₂ τ₃ τ₄ τ₅ : cpstyp} →
            {v₁  : var τ → cpsvalue𝑐[ var ] (τ₂ ⇒[ τ₁ ⇒ τ₃ ]⇒ τ₄) } →
            {v₂  : var τ → cpsvalue𝑐[ var ] τ₂ } →
            {k₃  : var τ → cpscont𝑐[ var ] (τ₅ ⇒ τ₅) (τ₁ ⇒ τ₃) } →
            {v   : cpsvalue𝑐[ var ] τ } →
            {v₁′ : cpsvalue𝑐[ var ] (τ₂ ⇒[ τ₁ ⇒ τ₃ ]⇒ τ₄) } →
            {v₂′ : cpsvalue𝑐[ var ] τ₂ } →
            {k₃′ : cpscont𝑐[ var ] (τ₅ ⇒ τ₅) (τ₁ ⇒ τ₃) } →
            cpsSubstValV𝑐 (λ x → (v₁ x)) v v₁′ →
            cpsSubstValV𝑐 (λ x → (v₂ x)) v v₂′ →
            cpsSubstContV𝑐 (λ k → (k₃ k)) v k₃′ → 
            cpsSubstV𝑐 (λ x → CPSApp (v₁ x) (v₂ x) (k₃ x)) v (CPSApp v₁′ v₂′ k₃′)
    sRet  : {τ τ₁ τ₂ τ₃ : cpstyp} →
            {k₁  : var τ → cpscont𝑐[ var ] (τ₃ ⇒ τ₃) (τ₁ ⇒ τ₂)} →
            {v₂  : var τ → cpsvalue𝑐[ var ] τ₁} →
            {v   : cpsvalue𝑐[ var ] τ} →
            {k₁′ : cpscont𝑐[ var ] (τ₃ ⇒ τ₃) (τ₁ ⇒ τ₂)} →
            {v₂′ : cpsvalue𝑐[ var ] τ₁} →
            cpsSubstContV𝑐 k₁ v k₁′ → cpsSubstValV𝑐 v₂ v v₂′ →
            cpsSubstV𝑐 (λ x → CPSRet (k₁ x) (v₂ x)) v (CPSRet k₁′ v₂′)
    sRetE : {τ τ₀ τ₁ τ₂ τ₃ : cpstyp} →
            {k₁  : var τ → cpscont𝑐[ var ] (τ₃ ⇒ τ₃) (τ₁ ⇒ τ₂)} →
            {e₂  : var τ → cpsterm𝑐[ var ] (τ₀ ⇒ τ₀) τ₁} →
            {v   : cpsvalue𝑐[ var ] τ} →
            {k₁′ : cpscont𝑐[ var ] (τ₃ ⇒ τ₃) (τ₁ ⇒ τ₂)} →
            {e₂′ : cpsterm𝑐[ var ] (τ₀ ⇒ τ₀) τ₁} →
            cpsSubstContV𝑐 k₁ v k₁′ → cpsSubstV𝑐 (λ x → e₂ x) v e₂′ → 
            cpsSubstV𝑐 (λ x → CPSRetE (k₁ x) (e₂ x)) v (CPSRetE k₁′ e₂′)

  data cpsSubstContV𝑐 {var : cpstyp → Set} : {τ τ₁ τ₂ τ₃ : cpstyp} →
                      (var τ → cpscont𝑐[ var ] (τ₃ ⇒ τ₃) (τ₁ ⇒ τ₂)) →
                      cpsvalue𝑐[ var ] τ →
                      cpscont𝑐[ var ] (τ₃ ⇒ τ₃) (τ₁ ⇒ τ₂) → Set where
    sKVar≠ : {τ τ₁ τ₂ : cpstyp}
             {v : cpsvalue𝑐[ var ] τ} {k′ : var (τ₁ ⇒[ (τ₂ ⇒ τ₂) ]⇒ τ₂)} →
             cpsSubstContV𝑐 (λ _ → CPSKVar k′) v (CPSKVar k′)
    sKId   : {τ τ₁ : cpstyp} {v : cpsvalue𝑐[ var ] τ} →
             cpsSubstContV𝑐 {τ₁ = τ₁} (λ _ → CPSId) v CPSId
    sKFun  : {τ τ₁ τ₂ τ₄ : cpstyp} →
             {e₁ : var τ → var τ₁ → cpsterm𝑐[ var ] (τ₄ ⇒ τ₄) τ₂ } → 
             {v  : cpsvalue𝑐[ var ] τ} →
             {e₁′ : var τ₁ → cpsterm𝑐[ var ] (τ₄ ⇒ τ₄) τ₂ } → 
             ((x₁ : var τ₁) → cpsSubstV𝑐 (λ x → (e₁ x) x₁) v (e₁′ x₁)) →
             cpsSubstContV𝑐 (λ x → CPSCont (e₁ x)) v (CPSCont e₁′)


-- 値と継続の代入規則
mutual
  -- data cpsSubstVal𝑐 {var : cpstyp → Set} : {τ τ₁ α β γ : cpstyp} →
  --                   (var τ → var (α ⇒[ (β ⇒ γ) ]⇒ γ) → cpsvalue𝑐[ var ] τ₁) →
  --                   cpsvalue𝑐[ var ] τ →
  --                   cpscont𝑐[ var ] (γ ⇒ γ) (α ⇒ β) → 
  --                   cpsvalue𝑐[ var ] τ₁ → Set where
  --   sVar=  : {τ α β γ : cpstyp} {v : cpsvalue𝑐[ var ] τ} {c : cpscont𝑐[ var ] (γ ⇒ γ) (α ⇒ β)} →
  --            cpsSubstVal𝑐 (λ x _ → CPSVar x) v c v
  --   sVar≠  : {τ τ₁ α β γ : cpstyp}
  --            {v : cpsvalue𝑐[ var ] τ} {c : cpscont𝑐[ var ] (γ ⇒ γ) (α ⇒ β)} {x : var τ₁} →
  --            cpsSubstVal𝑐 (λ _ _ → CPSVar x) v c (CPSVar x)
  --   sNum   : {τ α β γ : cpstyp}
  --            {v : cpsvalue𝑐[ var ] τ} {c : cpscont𝑐[ var ] (γ ⇒ γ) (α ⇒ β)} {n : ℕ} →
  --            cpsSubstVal𝑐 (λ _ _ → CPSNum n) v c (CPSNum n)
  --   sShift : {τ α β γ τ₁ τ₂ τ₃ τ₄ τ₅ : cpstyp} →
  --            {v : cpsvalue𝑐[ var ] τ} {c : cpscont𝑐[ var ] (γ ⇒ γ) (α ⇒ β)} →
  --            cpsSubstVal𝑐 (λ _ _ → CPSShift {τ₁ = τ₁} {τ₂} {τ₃} {τ₄} {τ₅}) v c CPSShift
  --   sFun   : {τ₀ τ τ₁ τ₂ τ₃ τ₄ α β γ : cpstyp} →
  --            {e : var τ → var (α ⇒[ (β ⇒ γ) ]⇒ γ) →
  --                 var τ₂ → var (τ₁ ⇒[ (τ₃ ⇒ τ₃) ]⇒ τ₃) → cpsterm𝑐[ var ] (τ₃ ⇒ τ₃) τ₄} → 
  --            {v : cpsvalue𝑐[ var ] τ} →
  --            {c : cpscont𝑐[ var ] (γ ⇒ γ) (α ⇒ β)} →
  --            {e′ : var τ₂ → var (τ₁ ⇒[ (τ₃ ⇒ τ₃) ]⇒ τ₃) → cpsterm𝑐[ var ] (τ₃ ⇒ τ₃) τ₄} → 
  --            ((x : var τ₂) → (k : var (τ₁ ⇒[ (τ₃ ⇒ τ₃) ]⇒ τ₃)) →
  --            cpsSubst𝑐 (λ y k₂ → (e y k₂) x k) v c (e′ x k)) → 
  --            cpsSubstVal𝑐 (λ y k₂ → CPSFun (λ x k → (e y k₂) x k))
  --                          v c
  --                        (CPSFun (λ x k → e′ x k))


-- 継続の型はこれでいいのか...?
  data cpsSubst𝑐 {var : cpstyp → Set} : {τ τ₁ τ₃ α β γ : cpstyp} →
                 (var τ → var (α ⇒[ (β ⇒ γ) ]⇒ γ) → cpsterm𝑐[ var ] (τ₃ ⇒ τ₃) τ₁) →
                 cpsvalue𝑐[ var ] τ →
                 cpscont𝑐[ var ] (γ ⇒ γ) (α ⇒ β) → 
                 cpsterm𝑐[ var ] (τ₃ ⇒ τ₃) τ₁ → Set where

    sApp  : {τ τ₁ τ₂ τ₃ τ₄ τ₅ α β γ : cpstyp} →
            {v₁  : var τ → cpsvalue𝑐[ var ] (τ₂ ⇒[ τ₁ ⇒ τ₃ ]⇒ τ₄) } →
            {v₂  : var τ → cpsvalue𝑐[ var ] τ₂ } →
            {k₃  : var τ → var (α ⇒[ (β ⇒ γ) ]⇒ γ) → cpscont𝑐[ var ] (τ₅ ⇒ τ₅) (τ₁ ⇒ τ₃) } →
            {v   : cpsvalue𝑐[ var ] τ } →
            {c   : cpscont𝑐[ var ] (γ ⇒ γ) (α ⇒ β) } →
            {v₁′ : cpsvalue𝑐[ var ] (τ₂ ⇒[ τ₁ ⇒ τ₃ ]⇒ τ₄) } → 
            {v₂′ : cpsvalue𝑐[ var ] τ₂ } →
            {k₃′ : cpscont𝑐[ var ] (τ₅ ⇒ τ₅) (τ₁ ⇒ τ₃) } →
            cpsSubstValV𝑐 v₁ v v₁′ →
            cpsSubstValV𝑐 v₂ v v₂′ →
            cpsSubstCont𝑐 k₃ v c k₃′ → 
            cpsSubst𝑐 (λ x k → CPSApp (v₁ x) (v₂ x) (k₃ x k)) v c (CPSApp v₁′ v₂′ k₃′)

    sRet  : {τ τ₁ τ₂ τ₃ α β γ : cpstyp} →
            {k₁  : var τ → var (α ⇒[ (β ⇒ γ) ]⇒ γ) → cpscont𝑐[ var ] (τ₃ ⇒ τ₃) (τ₁ ⇒ τ₂)} →
            {v₂  : var τ → cpsvalue𝑐[ var ] τ₁} →
            {v   : cpsvalue𝑐[ var ] τ} →
            {c   : cpscont𝑐[ var ] (γ ⇒ γ) (α ⇒ β)} → 
            {k₁′ : cpscont𝑐[ var ] (τ₃ ⇒ τ₃) (τ₁ ⇒ τ₂)} →
            {v₂′ : cpsvalue𝑐[ var ] τ₁} →
            cpsSubstCont𝑐 k₁ v c k₁′ → cpsSubstValV𝑐 v₂ v v₂′ →
            cpsSubst𝑐 (λ x k → CPSRet (k₁ x k) (v₂ x)) v c (CPSRet k₁′ v₂′)

    sRetE : {τ τ₀ τ₁ τ₂ τ₃ α β γ : cpstyp} →
            {k₁  : var τ → var (α ⇒[ (β ⇒ γ) ]⇒ γ) → cpscont𝑐[ var ] (τ₃ ⇒ τ₃) (τ₁ ⇒ τ₂)} →
            {e₂  : var τ → var (α ⇒[ (β ⇒ γ) ]⇒ γ) → cpsterm𝑐[ var ] (τ₀ ⇒ τ₀) τ₁} →
            {v   : cpsvalue𝑐[ var ] τ} →
            {c   : cpscont𝑐[ var ] (γ ⇒ γ) (α ⇒ β)} → 
            {k₁′ : cpscont𝑐[ var ] (τ₃ ⇒ τ₃) (τ₁ ⇒ τ₂)} →
            {e₂′ : cpsterm𝑐[ var ] (τ₀ ⇒ τ₀) τ₁} →
            cpsSubstCont𝑐 k₁ v c k₁′ → cpsSubst𝑐 (λ x k → e₂ x k) v c e₂′ → 
            cpsSubst𝑐 (λ x k → CPSRetE (k₁ x k) (e₂ x k)) v c (CPSRetE k₁′ e₂′)

  data cpsSubstCont𝑐 {var : cpstyp → Set} : {τ τ₁ τ₂ τ₃ α β γ : cpstyp} →
                     (var τ → var (α ⇒[ (β ⇒ γ) ]⇒ γ) → cpscont𝑐[ var ] (τ₃ ⇒ τ₃) (τ₁ ⇒ τ₂)) →
                     cpsvalue𝑐[ var ] τ →
                     cpscont𝑐[ var ] (γ ⇒ γ) (α ⇒ β) → 
                     cpscont𝑐[ var ] (τ₃ ⇒ τ₃) (τ₁ ⇒ τ₂) → Set where
    sKVar= : {τ α β : cpstyp} {v : cpsvalue𝑐[ var ] τ} {c : cpscont𝑐[ var ] (β ⇒ β) (α ⇒ β)} →
             cpsSubstCont𝑐 (λ _ k → CPSKVar k) v c c
    sKVar≠ : {τ α β γ τ₁ τ₂ : cpstyp}
             {v : cpsvalue𝑐[ var ] τ}
             {c : cpscont𝑐[ var ] (γ ⇒ γ) (α ⇒ β)} {k′ : var (τ₁ ⇒[ (τ₂ ⇒ τ₂) ]⇒ τ₂)} →
             cpsSubstCont𝑐 (λ _ _ → CPSKVar k′) v c (CPSKVar k′)
    sKId   : {τ α β γ τ₁ : cpstyp} →
             {v : cpsvalue𝑐[ var ] τ} {c : cpscont𝑐[ var ] (γ ⇒ γ) (α ⇒ β)} →
             cpsSubstCont𝑐 {τ₁ = τ₁} (λ _ _ → CPSId) v c CPSId
    sKFun  : {τ τ₁ τ₂ τ₄ α β γ : cpstyp} →
             {e₁ : var τ → var (α ⇒[ (β ⇒ γ) ]⇒ γ) → var τ₁ → cpsterm𝑐[ var ] (τ₄ ⇒ τ₄) τ₂} → 
             {v  : cpsvalue𝑐[ var ] τ} → 
             {c  : cpscont𝑐[ var ] (γ ⇒ γ) (α ⇒ β)} →
             {e₁′ : var τ₁ → cpsterm𝑐[ var ] (τ₄ ⇒ τ₄) τ₂} → 
             ((x₁ : var τ₁) → cpsSubst𝑐 (λ x k → (e₁ x k) x₁) v c (e₁′ x₁)) →
             cpsSubstCont𝑐 (λ x k → CPSCont (e₁ x k)) v c (CPSCont e₁′)

data cpsReduceR {var : cpstyp → Set}  :
                {τ₁ τ₂ τ₃ : cpstyp} →
                (var (τ₁ ⇒[ (τ₂ ⇒ τ₂) ]⇒ τ₂) → cpsterm𝑐[ var ] (τ₂ ⇒ τ₂) τ₃) →
                (var (τ₁ ⇒[ (τ₂ ⇒ τ₂) ]⇒ τ₂) → cpsterm𝑐[ var ] (τ₂ ⇒ τ₂) τ₃) → Set where
     βVal𝑐   : {τ τ′ τ₁ τ₂ τ₃ : cpstyp} →
               {e₁ : var τ → var (τ′ ⇒[ (τ₂ ⇒ τ₂) ]⇒ τ₂) → cpsterm𝑐[ var ] (τ₂ ⇒ τ₂) τ₃} →
               {v : cpsvalue𝑐[ var ] τ} →
               {c : cpscont𝑐[ var ] (τ₂ ⇒ τ₂) (τ′ ⇒ τ₂)} →
               {e₂ : cpsterm𝑐[ var ] (τ₂ ⇒ τ₂) τ₃} →
               cpsSubst𝑐 e₁ v c e₂ →
               cpsReduceR {τ₁ = τ₁} (λ k → CPSApp (CPSFun (λ x k′ → e₁ x k′)) v c) (λ k → e₂)
     -- RTrans𝑐 : {τ₁ τ₂ τ₃ : cpstyp} →
     --           (e₁ e₂ e₃ : var (τ₁ ⇒[ (τ₂ ⇒ τ₂) ]⇒ τ₂) → cpsterm𝑐[ var ] (τ₂ ⇒ τ₂) τ₃) → 
     --           cpsReduceR e₁ e₂ →
     --           cpsReduceR e₂ e₃ →
     --           cpsReduceR e₁ e₃
     -- RId𝑐    : {τ₁ τ₂ τ₃ : cpstyp} →
     --           {e : var (τ₁ ⇒[ (τ₂ ⇒ τ₂) ]⇒ τ₂) → cpsterm𝑐[ var ] (τ₂ ⇒ τ₂) τ₃} →
     --           cpsReduceR e e


 
data cpsReduce {var : cpstyp → Set}  :
               {τ₁ τ₂ : cpstyp} →
               cpsterm𝑐[ var ] (τ₂ ⇒ τ₂) τ₁ →
               cpsterm𝑐[ var ] (τ₂ ⇒ τ₂) τ₁ → Set where
     βLet𝑐    : {τ₁ τ₂ τ₄ : cpstyp} →
                {v : cpsvalue𝑐[ var ] τ₁} →
                {e : var τ₁ → cpsterm𝑐[ var ] (τ₄ ⇒ τ₄) τ₂} →
                {e′ : cpsterm𝑐[ var ] (τ₄ ⇒ τ₄) τ₂} →
                cpsSubstV𝑐 e v e′ → 
                cpsReduce (CPSRet (CPSCont (λ x → e x)) v) e′

     βShift𝑐  : {τ₁ τ₂ τ₃ τ₄ τ₅ : cpstyp} →
                {w : cpsvalue𝑐[ var ] ((τ₁ ⇒[ τ₂ ⇒ τ₃ ]⇒ τ₃) ⇒[ τ₄ ⇒ τ₄ ]⇒ τ₅)} →
                {j : cpscont𝑐[ var ] (τ₄ ⇒ τ₄) (τ₁ ⇒ τ₂)} → 
                cpsReduce (CPSApp CPSShift w j)
                          (CPSApp w (CPSFun (λ x k → CPSRetE (CPSKVar k) (CPSRet j (CPSVar x)))) CPSId)
     RTrans𝑐 : {τ₁ τ₂ : cpstyp} →
               (e₁ e₂ e₃ : cpsterm𝑐[ var ] (τ₂ ⇒ τ₂) τ₁) → 
               cpsReduce e₁ e₂ →
               cpsReduce e₂ e₃ →
               cpsReduce e₁ e₃
     RId𝑐    : {τ₁ τ₂ : cpstyp} →
               {e : cpsterm𝑐[ var ] (τ₂ ⇒ τ₂) τ₁} →
               cpsReduce e e

data cpsReduce• {var : cpstyp → Set} :
                {τ₁ τ₂ : cpstyp} →
                cpsterm𝑐[ var ] (τ₂ ⇒ τ₂) τ₁ →
                cpsterm𝑐[ var ] (τ₂ ⇒ τ₂) τ₁ → Set where
     βShift𝑐  : {τ₁ τ₂ τ₃ τ₄ τ₅ : cpstyp} →
                {w : cpsvalue𝑐[ var ] ((τ₁ ⇒[ τ₂ ⇒ τ₃ ]⇒ τ₃) ⇒[ τ₄ ⇒ τ₄ ]⇒ τ₅)} →
                {j : cpscont𝑐[ var ] (τ₄ ⇒ τ₄) (τ₁ ⇒ τ₂)} → 
                cpsReduce• (CPSApp CPSShift w j)
                           (CPSApp w (CPSFun (λ x k → CPSRetE (CPSKVar k) (CPSRet j (CPSVar x)))) CPSId)


data cpsReduceV {var : cpstyp → Set}  :
                 {τ₁ : cpstyp} →
                 cpsvalue𝑐[ var ] τ₁ →
                 cpsvalue𝑐[ var ] τ₁ → Set where
     ηVal𝑐 : {τ₁ τ₂ τ₃ τ₄ : cpstyp} →
             {v : cpsvalue𝑐[ var ] (τ₂ ⇒[ τ₁ ⇒ τ₃ ]⇒ τ₄)} →
             cpsReduceV (CPSFun (λ x k → CPSApp v (CPSVar x) (CPSKVar k))) v

data cpsReduceK {var : cpstyp → Set}  :
                {τ₁ τ₂ τ₃ : cpstyp} →
                cpscont𝑐[ var ] (τ₃ ⇒ τ₃) (τ₁ ⇒ τ₂) →
                cpscont𝑐[ var ] (τ₃ ⇒ τ₃) (τ₁ ⇒ τ₂) → Set where
     ηLet𝑐 : {τ₁ τ₂ τ₃ : cpstyp} →
             {k : cpscont𝑐[ var ] (τ₃ ⇒ τ₃) (τ₁ ⇒ τ₂)} →
             cpsReduceK (CPSCont (λ x → CPSRet k (CPSVar x))) k

{-
       -- RReset   : {τ₁ τ₂ : cpstyp} →
       --            {v₂ : cpsvalue𝑐[ var ] {!!}} →
       --            -- cpsReduce (CPSRet (CPSId (λ x → CPSVar x)) {!!}) {!v₂!}
       RId𝑐     : {τ₁ τ₂ τ₃ : cpstyp} →
                  {e : cpsterm𝑐[ var ] (τ₂ ⇒ τ₃) τ₁} →
                  cpsReduce e e
       RTrans𝑐  : {τ₁ τ₂ τ₃ : cpstyp} →
                  (e₁ e₂ e₃ : cpsterm𝑐[ var ] (τ₂ ⇒ τ₃) τ₁) →
                  cpsReduce e₁ e₂ →
                  cpsReduce e₂ e₃ →
                  cpsReduce e₁ e₃
       RTrans𝑐′ : {τ₁ τ₂ τ₃ : cpstyp} →
                  (e₁ e₂ e₃ : cpsterm𝑐[ var ] (τ₂ ⇒ τ₃) τ₁) →
                  cpsReduce e₂ e₁ →
                  cpsReduce e₂ e₃ →
                  cpsReduce e₁ e₃

-}
