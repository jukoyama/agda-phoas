module CPSterm where

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
  data cpscont𝑐[_,_] (var : cpstyp → Set) (cvar : cpstyp → conttyp → Set) : conttyp → conttyp → Set where
    -- CPSKVar で τ₂ を τ にすると、DS変換の
    -- dsC𝑐 の CPSKVar のケースで τ が何かわからなくなる
    CPSKVar : {τ₁ τ₂ : cpstyp} → cvar τ₂ (τ₁ ⇒ τ₂) →
              cpscont𝑐[ var , cvar ] (τ₂ ⇒ τ₂) (τ₁ ⇒ τ₂)
    CPSId   : {τ₁ : cpstyp} → cpscont𝑐[ var , cvar ] (τ₁ ⇒ τ₁) (τ₁ ⇒ τ₁)
    CPSCont : {τ₁ τ₂ τ₃ τ₄ : cpstyp} → (var τ₁ → cpsterm𝑐[ var , cvar ] (τ₃ ⇒ τ₄) τ₂) →
              cpscont𝑐[ var , cvar ] (τ₃ ⇒ τ₄) (τ₁ ⇒ τ₂)

  data cpsvalue𝑐[_,_] (var : cpstyp → Set) (cvar : cpstyp → conttyp → Set) : cpstyp → Set where
    CPSVar : {τ₁ : cpstyp} → var τ₁ → cpsvalue𝑐[ var , cvar ] τ₁
    CPSNum : ℕ → cpsvalue𝑐[ var , cvar ] Nat
    CPSFun : {τ τ₁ τ₂ τ₃ τ₄ : cpstyp} →
             (var τ₂ → cvar τ (τ₁ ⇒ τ₃) → cpsterm𝑐[ var , cvar ] (τ₁ ⇒ τ₃) τ₄) →
             cpsvalue𝑐[ var , cvar ] (τ₂ ⇒[ τ₁ ⇒ τ₃ ]⇒ τ₄)
    CPSShift : {τ₁ τ₂ τ₃ τ₄ τ₅ : cpstyp} →
               cpsvalue𝑐[ var , cvar ]
                 (((τ₁ ⇒[ τ₂ ⇒ τ₃ ]⇒ τ₃) ⇒[ τ₄ ⇒ τ₄ ]⇒ τ₅) ⇒[ τ₁ ⇒ τ₂ ]⇒ τ₅)

  data cpsterm𝑐[_,_] (var : cpstyp → Set) (cvar : cpstyp → conttyp → Set) : conttyp → cpstyp → Set where
    CPSRet : {τ₁ τ₂ τ₃ τ₄ : cpstyp} →
             cpscont𝑐[ var , cvar ] (τ₃ ⇒ τ₄) (τ₁ ⇒ τ₂) →
             cpsvalue𝑐[ var , cvar ] τ₁ →
             cpsterm𝑐[ var , cvar ] (τ₃ ⇒ τ₄) τ₂
    CPSApp : {τ₁ τ₂ τ₃ τ₄ τ₅ τ₆ : cpstyp} →
             cpsvalue𝑐[ var , cvar ] (τ₂ ⇒[ τ₁ ⇒ τ₃ ]⇒ τ₄) →
             cpsvalue𝑐[ var , cvar ] τ₂ →
             cpscont𝑐[ var , cvar ] (τ₅ ⇒ τ₆) (τ₁ ⇒ τ₃) →
             cpsterm𝑐[ var , cvar ] (τ₅ ⇒ τ₆) τ₄
    CPSRetE : {τ₀ τ₁ τ₂ τ₃ τ₄ : cpstyp} →
             cpscont𝑐[ var , cvar ] (τ₃ ⇒ τ₄) (τ₁ ⇒ τ₂) →
             cpsterm𝑐[ var , cvar ] (τ₀ ⇒ τ₀) τ₁ →
             cpsterm𝑐[ var , cvar ] (τ₃ ⇒ τ₄) τ₂
             
-- 値と継続の代入規則
mutual
  data cpsSubstVal𝑐 {var : cpstyp → Set} {cvar : cpstyp → conttyp → Set} : {τ τ₁ α β γ δ : cpstyp} →
                    (var τ → cvar β (α ⇒ β) → cpsvalue𝑐[ var , cvar ] τ₁) →
                    cpsvalue𝑐[ var , cvar ] τ →
                    cpscont𝑐[ var , cvar ] (γ ⇒ δ) (α ⇒ β) → 
                    cpsvalue𝑐[ var , cvar ] τ₁ → Set where
    sVar= : {τ α β γ δ : cpstyp} {v : cpsvalue𝑐[ var , cvar ] τ} {c : cpscont𝑐[ var , cvar ] (γ ⇒ δ) (α ⇒ β)} →
            cpsSubstVal𝑐 (λ x _ → CPSVar x) v c v
    sVar≠ : {τ τ₁ α β γ δ : cpstyp}
            {v : cpsvalue𝑐[ var , cvar ] τ} {c : cpscont𝑐[ var , cvar ] (γ ⇒ δ) (α ⇒ β)} {x : var τ₁} →
            cpsSubstVal𝑐 (λ _ _ → CPSVar x) v c (CPSVar x)
    sNum  : {τ α β γ δ : cpstyp}
            {v : cpsvalue𝑐[ var , cvar ] τ} {c : cpscont𝑐[ var , cvar ] (γ ⇒ δ) (α ⇒ β)} {n : ℕ} →
            cpsSubstVal𝑐 (λ _ _ → CPSNum n) v c (CPSNum n)
    sFun  : {τ₀ τ τ₁ τ₂ τ₃ τ₄ α β γ δ : cpstyp} →
            {e : var τ → cvar β (α ⇒ β) → var τ₂ → cvar τ₃ (τ₁ ⇒ τ₃) → cpsterm𝑐[ var , cvar ] (τ₁ ⇒ τ₃) τ₄} → 
            {v : cpsvalue𝑐[ var , cvar ] τ} →
            {c : cpscont𝑐[ var , cvar ] (γ ⇒ δ) (α ⇒ β)} →
            {e′ : var τ₂ → cvar τ₃ (τ₁ ⇒ τ₃) → cpsterm𝑐[ var , cvar ] (τ₁ ⇒ τ₃) τ₄} → 
            ((x : var τ₂) → (k : cvar τ₃ (τ₁ ⇒ τ₃)) →
            cpsSubst𝑐 (λ y k₂ → (e y k₂) x k) v c (e′ x k)) → 
            cpsSubstVal𝑐 (λ y k₂ → CPSFun (λ x k → (e y k₂) x k))
                         v c
                         (CPSFun (λ x k → e′ x k))

-- 継続の型はこれでいいのか...?
  data cpsSubst𝑐 {var : cpstyp → Set} {cvar : cpstyp → conttyp → Set} : {τ τ₁ τ₂ τ₃ α β γ δ : cpstyp} →
                 (var τ → cvar β (α ⇒ β) → cpsterm𝑐[ var , cvar ] (τ₂ ⇒ τ₃) τ₁) →
                 cpsvalue𝑐[ var , cvar ] τ →
                 cpscont𝑐[ var , cvar ] (γ ⇒ δ) (α ⇒ β) → 
                 cpsterm𝑐[ var , cvar ] (τ₂ ⇒ τ₃) τ₁ → Set where
    -- k₃ の持ち歩く型はこれでいいのか...?
    sApp  : {τ τ₁ τ₂ τ₃ τ₄ τ₅ τ₆ α β γ δ : cpstyp} →
            {v₁  : var τ → cvar β (α ⇒ β) → cpsvalue𝑐[ var , cvar ] (τ₂ ⇒[ τ₁ ⇒ τ₃ ]⇒ τ₄) } →
            {v₂  : var τ → cvar β (α ⇒ β) → cpsvalue𝑐[ var , cvar ] τ₂ } →
            {k₃  : var τ → cvar β (α ⇒ β) → cpscont𝑐[ var , cvar ] (τ₆ ⇒ τ₅) (τ₁ ⇒ τ₃) } →
            {v   : cpsvalue𝑐[ var , cvar ] τ } →
            {c   : cpscont𝑐[ var , cvar ] (γ ⇒ δ) (α ⇒ β) } →
            {v₁′ : cpsvalue𝑐[ var , cvar ] (τ₂ ⇒[ τ₁ ⇒ τ₃ ]⇒ τ₄) } → 
            {v₂′ : cpsvalue𝑐[ var , cvar ] τ₂ } →
            {k₃′ : cpscont𝑐[ var , cvar ] (τ₆ ⇒ τ₅) (τ₁ ⇒ τ₃) } →
            cpsSubstVal𝑐 (λ x → (v₁ x)) v c v₁′ →
            cpsSubstVal𝑐 (λ x → (v₂ x)) v c v₂′ →
            cpsSubstCont𝑐 (λ k → (k₃ k)) v c k₃′ → 
            cpsSubst𝑐 (λ x k → CPSApp (v₁ x k) (v₂ x k) (k₃ x k)) v c (CPSApp v₁′ v₂′ k₃′)           
    sRet  : {τ τ₁ τ₂ τ₃ τ₄ α β γ δ : cpstyp} →
            {k₁  : var τ → cvar β (α ⇒ β) → cpscont𝑐[ var , cvar ] (τ₃ ⇒ τ₄) (τ₁ ⇒ τ₂)} →
            {v₂  : var τ → cvar β (α ⇒ β) → cpsvalue𝑐[ var , cvar ] τ₁} →
            {v   : cpsvalue𝑐[ var , cvar ] τ} →
            {c   : cpscont𝑐[ var , cvar ] (γ ⇒ δ) (α ⇒ β)} → 
            {k₁′ : cpscont𝑐[ var , cvar ] (τ₃ ⇒ τ₄) (τ₁ ⇒ τ₂)} →
            {v₂′ : cpsvalue𝑐[ var , cvar ] τ₁} →
            cpsSubstCont𝑐 k₁ v c k₁′ → cpsSubstVal𝑐 v₂ v c v₂′ →
            cpsSubst𝑐 (λ x k → CPSRet (k₁ x k) (v₂ x k)) v c (CPSRet k₁′ v₂′)
    sRetE : {τ τ₀ τ₁ τ₂ τ₃ τ₄ α β γ δ : cpstyp} →
            {k₁  : var τ → cvar β (α ⇒ β) → cpscont𝑐[ var , cvar ] (τ₃ ⇒ τ₄) (τ₁ ⇒ τ₂)} →
            {e₂  : var τ → cvar β (α ⇒ β) → cpsterm𝑐[ var , cvar ] (τ₀ ⇒ τ₀) τ₁} →
            {v   : cpsvalue𝑐[ var , cvar ] τ} →
            {c   : cpscont𝑐[ var , cvar ] (γ ⇒ δ) (α ⇒ β)} → 
            {k₁′ : cpscont𝑐[ var , cvar ] (τ₃ ⇒ τ₄) (τ₁ ⇒ τ₂)} →
            {e₂′ : cpsterm𝑐[ var , cvar ] (τ₀ ⇒ τ₀) τ₁} →
            cpsSubstCont𝑐 k₁ v c k₁′ → cpsSubst𝑐 (λ x k → e₂ x k) v c e₂′ → 
            cpsSubst𝑐 (λ x k → CPSRetE (k₁ x k) (e₂ x k)) v c (CPSRetE k₁′ e₂′)

  data cpsSubstCont𝑐 {var : cpstyp → Set} {cvar : cpstyp → conttyp → Set} : {τ α β γ δ τ₄ τ₅ τ₆ τ₇ : cpstyp} →
                     (var τ → cvar β (α ⇒ β) → cpscont𝑐[ var , cvar ] (τ₆ ⇒ τ₇) (τ₄ ⇒ τ₅)) →
                     cpsvalue𝑐[ var , cvar ] τ →
                     cpscont𝑐[ var , cvar ] (γ ⇒ δ) (α ⇒ β) → 
                     cpscont𝑐[ var , cvar ] (τ₆ ⇒ τ₇) (τ₄ ⇒ τ₅) → Set where
    sKVar= : {τ α β γ δ : cpstyp} {v : cpsvalue𝑐[ var , cvar ] τ} {c : cpscont𝑐[ var , cvar ] (β ⇒ β) (τ ⇒ β)} →
             cpsSubstCont𝑐 (λ _ k → CPSKVar k) v c c
    sKVar≠ : {τ α β τ₁ τ₂ : cpstyp}
             {v : cpsvalue𝑐[ var , cvar ] τ}
             {c : cpscont𝑐[ var , cvar ] (α ⇒ β) (α ⇒ β)} {k′ : cvar τ₂ (τ₁ ⇒ τ₂)} →
             cpsSubstCont𝑐 (λ _ k → CPSKVar k′) v c (CPSKVar k′)
    sKFun  : {τ₀ τ τ₁ τ₂ τ₃ τ₄ τ₅ α β γ δ : cpstyp} →
             {e₁ : var τ → cvar β (α ⇒ β) → var τ₁ → cpsterm𝑐[ var , cvar ] (τ₃ ⇒ τ₄) τ₂} → 
             {v  : cpsvalue𝑐[ var , cvar ] τ} → 
             {c  : cpscont𝑐[ var , cvar ] (γ ⇒ δ) (α ⇒ β)} →
             {e₁′ : var τ₁ → cpsterm𝑐[ var , cvar ] (τ₃ ⇒ τ₄) τ₂} → 
             ((x₁ : var τ₁) → cpsSubst𝑐 (λ x k → (e₁ x k) x₁) v c (e₁′ x₁)) →
             cpsSubstCont𝑐 (λ x k → CPSCont (e₁ x k)) v c (CPSCont e₁′)

-- 値による代入規則
mutual
  data cpsSubstValK𝑐 {var : cpstyp → Set} {cvar : cpstyp → conttyp → Set} : {τ τ₁ : cpstyp} →
                     (var τ → cpsvalue𝑐[ var , cvar ] τ₁) →
                     cpsvalue𝑐[ var , cvar ] τ →
                     cpsvalue𝑐[ var , cvar ] τ₁ → Set where
    sVar= : {τ : cpstyp} {v : cpsvalue𝑐[ var , cvar ] τ} →
            cpsSubstValK𝑐 (λ x → CPSVar x) v v
    sVar≠ : {τ τ₁ : cpstyp} {v : cpsvalue𝑐[ var , cvar ] τ} {x : var τ₁} →
            cpsSubstValK𝑐 (λ _ → CPSVar x) v (CPSVar x)
    sNum  : {τ : cpstyp} {v : cpsvalue𝑐[ var , cvar ] τ}  {n : ℕ} →
            cpsSubstValK𝑐 (λ _ → CPSNum n) v (CPSNum n)
    sFun  : {τ τ′ τ₁ τ₂ τ₃ τ₄ : cpstyp} →
            {e  : var τ →  var τ₂ → cvar τ′ (τ₁ ⇒ τ₃) → cpsterm𝑐[ var , cvar ] (τ₁ ⇒ τ₃) τ₄} → 
            {v  : cpsvalue𝑐[ var , cvar ] τ} →
            {e′ : var τ₂ → cvar τ′ (τ₁ ⇒ τ₃) → cpsterm𝑐[ var , cvar ] (τ₁ ⇒ τ₃) τ₄} → 
            ((x : var τ₂) → (k : cvar τ′ (τ₁ ⇒ τ₃)) →
              cpsSubstK𝑐 (λ y → (e y) x k) v (e′ x k)) → 
            cpsSubstValK𝑐 (λ y → CPSFun (λ x k → (e y) x k)) v (CPSFun (λ x k → e′ x k))
            
  data cpsSubstK𝑐 {var : cpstyp → Set} {cvar : cpstyp → conttyp → Set} : {τ₁ τ₂ τ₃ τ₄ : cpstyp} →
                  (var τ₁ → cpsterm𝑐[ var , cvar ] (τ₃ ⇒ τ₄) τ₂) →
                  cpsvalue𝑐[ var , cvar ] τ₁ →
                  cpsterm𝑐[ var , cvar ] (τ₃ ⇒ τ₄) τ₂ → Set where
    sApp  : {τ τ₁ τ₂ τ₃ τ₄ τ₅ τ₆ : cpstyp} →
            {v₁  : var τ → cpsvalue𝑐[ var , cvar ] (τ₂ ⇒[ τ₁ ⇒ τ₃ ]⇒ τ₄) } →
            {v₂  : var τ → cpsvalue𝑐[ var , cvar ] τ₂ } →
            {k₃  : var τ → cpscont𝑐[ var , cvar ] (τ₆ ⇒ τ₅) (τ₁ ⇒ τ₃) } →
            {v   : cpsvalue𝑐[ var , cvar ] τ } →
            {v₁′ : cpsvalue𝑐[ var , cvar ] (τ₂ ⇒[ τ₁ ⇒ τ₃ ]⇒ τ₄) } →
            {v₂′ : cpsvalue𝑐[ var , cvar ] τ₂ } →
            {k₃′ : cpscont𝑐[ var , cvar ] (τ₆ ⇒ τ₅) (τ₁ ⇒ τ₃) } →
            cpsSubstValK𝑐 (λ x → (v₁ x)) v v₁′ →
            cpsSubstValK𝑐 (λ x → (v₂ x)) v v₂′ →
            cpsSubstContK𝑐 (λ k → (k₃ k)) v k₃′ → 
            cpsSubstK𝑐 (λ x → CPSApp (v₁ x) (v₂ x) (k₃ x)) v (CPSApp v₁′ v₂′ k₃′)           
    sRet  : {τ τ₁ τ₂ τ₃ τ₄ : cpstyp} →
            {k₁  : var τ → cpscont𝑐[ var , cvar ] (τ₄ ⇒ τ₃) (τ₂ ⇒ τ₁)} →
            {v₂  : var τ → cpsvalue𝑐[ var , cvar ] τ₂} →
            {v   : cpsvalue𝑐[ var , cvar ] τ} →
            {k₁′ : cpscont𝑐[ var , cvar ] (τ₄ ⇒ τ₃) (τ₂ ⇒ τ₁)} →
            {v₂′ : cpsvalue𝑐[ var , cvar ] τ₂} →
            cpsSubstContK𝑐 k₁ v k₁′ → cpsSubstValK𝑐 v₂ v v₂′ →
            cpsSubstK𝑐 (λ x → CPSRet (k₁ x) (v₂ x)) v (CPSRet k₁′ v₂′)
    sRetE : {τ τ₀ τ₁ τ₂ τ₃ τ₄ : cpstyp} →
            {k₁  : var τ → cpscont𝑐[ var , cvar ] (τ₄ ⇒ τ₃) (τ₂ ⇒ τ₁)} →
            {e₂  : var τ → cpsterm𝑐[ var , cvar ] (τ₀ ⇒ τ₀) τ₂} →
            {v   : cpsvalue𝑐[ var , cvar ] τ} →
            {k₁′ : cpscont𝑐[ var , cvar ] (τ₄ ⇒ τ₃) (τ₂ ⇒ τ₁)} →
            {e₂′ : cpsterm𝑐[ var , cvar ] (τ₀ ⇒ τ₀) τ₂} →
            cpsSubstContK𝑐 k₁ v k₁′ → cpsSubstK𝑐 (λ x → e₂ x) v e₂′ → 
            cpsSubstK𝑐 (λ x → CPSRetE (k₁ x) (e₂ x)) v (CPSRetE k₁′ e₂′)

  data cpsSubstContK𝑐 {var : cpstyp → Set} {cvar : cpstyp → conttyp → Set} : {τ τ₁ τ₂ τ₃ τ₄ : cpstyp} →
                      (var τ → cpscont𝑐[ var , cvar ] (τ₃ ⇒ τ₄) (τ₁ ⇒ τ₂)) →
                      cpsvalue𝑐[ var , cvar ] τ →
                      cpscont𝑐[ var , cvar ] (τ₃ ⇒ τ₄) (τ₁ ⇒ τ₂) → Set where
    sKvar≠ : {τ τ₁ τ₂ : cpstyp}
             {v : cpsvalue𝑐[ var , cvar ] τ} {k′ : cvar τ₂ (τ₁ ⇒ τ₂)} →
             cpsSubstContK𝑐 (λ _ → CPSKVar k′) v (CPSKVar k′)
    sKFun  : {τ₀ τ τ₁ τ₂ τ₃ τ₄ τ₅ : cpstyp} →
             {e₁ : var τ → var τ₁ → cpsterm𝑐[ var , cvar ] (τ₃ ⇒ τ₄) τ₂ } → 
             {v  : cpsvalue𝑐[ var , cvar ] τ} →
             {e₁′ : var τ₁ → cpsterm𝑐[ var , cvar ] (τ₃ ⇒ τ₄) τ₂ } → 
             ((x₁ : var τ₁) → cpsSubstK𝑐 (λ x → (e₁ x) x₁) v (e₁′ x₁)) →
             cpsSubstContK𝑐 (λ x → CPSCont (e₁ x)) v (CPSCont e₁′)


mutual 
  data cpsReduce {var : cpstyp → Set} {cvar : cpstyp → conttyp → Set} :
                 {τ₁ τ₂ τ₃ : cpstyp} →
                 cpsterm𝑐[ var , cvar ] (τ₂ ⇒ τ₃) τ₁ →
                 cpsterm𝑐[ var , cvar ] (τ₂ ⇒ τ₃) τ₁ → Set where
       RBeta𝑐   : {τ₁ τ₂ τ₃ τ₄ : cpstyp} →
                  {e₁ : var τ₂ → cvar τ₃ (τ₁ ⇒ τ₃) → cpsterm𝑐[ var , cvar ] (τ₁ ⇒ τ₃) τ₄} →
                  {v : cpsvalue𝑐[ var , cvar ] τ₂} →
                  -- τ₁ ⇒ τ₃ でいい...?
                  {c : cpscont𝑐[ var , cvar ] (τ₁ ⇒ τ₃) (τ₁ ⇒ τ₃)} →
                  {e₂ : cpsterm𝑐[ var , cvar ] (τ₁ ⇒ τ₃) τ₄} →
                  cpsSubst𝑐 e₁ v c e₂ →
                  cpsReduce (CPSApp (CPSFun (λ x k → e₁ x k)) v c) e₂
       RLet𝑐    : {τ₁ τ₂ τ₃ τ₄ : cpstyp} →
                  {v₁ : cpsvalue𝑐[ var , cvar ] τ₂} →
                  {e𝑐 : var τ₂ → cpsterm𝑐[ var , cvar ] (τ₄ ⇒ τ₃) τ₁} →
                  {e𝑐′ : cpsterm𝑐[ var , cvar ] (τ₄ ⇒ τ₃) τ₁} →
                  cpsSubstK𝑐 e𝑐 v₁ e𝑐′ → 
                  cpsReduce (CPSRet (CPSCont (λ x → e𝑐 x)) v₁) e𝑐′
       RShift𝑐  : {τ₁ τ₂ τ₃ τ₄ τ₅ : cpstyp} →
                  {v₂ : cpsvalue𝑐[ var , cvar ] ((τ₁ ⇒[ τ₂ ⇒ τ₂ ]⇒ τ₂) ⇒[ τ₄ ⇒ τ₄ ]⇒ τ₅)} →
                  {c₃ : cpscont𝑐[ var , cvar ] (τ₄ ⇒ τ₄) (τ₁ ⇒ τ₂)} → 
                  cpsReduce (CPSApp CPSShift v₂ c₃)
                            (CPSApp v₂ (CPSFun (λ x k → CPSRetE (CPSKVar k) (CPSRet c₃ (CPSVar x)))) CPSId)
       -- RReset   : {τ₁ τ₂ : cpstyp} →
       --            {v₂ : cpsvalue𝑐[ var , cvar ] {!!}} →
       --            -- cpsReduce (CPSRet (CPSId (λ x → CPSVar x)) {!!}) {!v₂!}
       RId𝑐     : {τ₁ τ₂ τ₃ : cpstyp} →
                  {e : cpsterm𝑐[ var , cvar ] (τ₂ ⇒ τ₃) τ₁} →
                  cpsReduce e e
       RTrans𝑐  : {τ₁ τ₂ τ₃ : cpstyp} →
                  (e₁ e₂ e₃ : cpsterm𝑐[ var , cvar ] (τ₂ ⇒ τ₃) τ₁) →
                  cpsReduce e₁ e₂ →
                  cpsReduce e₂ e₃ →
                  cpsReduce e₁ e₃
       RTrans𝑐′ : {τ₁ τ₂ τ₃ : cpstyp} →
                  (e₁ e₂ e₃ : cpsterm𝑐[ var , cvar ] (τ₂ ⇒ τ₃) τ₁) →
                  cpsReduce e₂ e₁ →
                  cpsReduce e₂ e₃ →
                  cpsReduce e₁ e₃


