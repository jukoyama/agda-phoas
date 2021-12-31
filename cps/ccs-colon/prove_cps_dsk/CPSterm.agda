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
  data cpscont𝑐[_] (var : cpstyp → Set) : conttyp → cpstyp → conttyp → Set where
    -- CPSKVar で τ₂ を τ にすると、DS変換の
    -- dsC𝑐 の CPSKVar のケースで τ が何かわからなくなる
    -- term の結果の型 τ₃ の情報も一緒に持ち合わせるようにした
    CPSKVar : {τ₁ τ₂ τ₃ : cpstyp} →
              var (τ₁ ⇒[ (τ₂ ⇒ τ₂) ]⇒ τ₂) →
              cpscont𝑐[ var ] (τ₂ ⇒ τ₂) τ₃ (τ₁ ⇒ τ₂)
    CPSId   : {τ₁ τ₃ : cpstyp} → cpscont𝑐[ var ] (τ₁ ⇒ τ₁) τ₃ (τ₁ ⇒ τ₁)
    CPSCont : {τ₁ τ₂ τ₃ τ₄ : cpstyp} → (var τ₁ → cpsterm𝑐[ var ] (τ₄ ⇒ τ₄) τ₂) →
              cpscont𝑐[ var ] (τ₄ ⇒ τ₄) τ₃ (τ₁ ⇒ τ₂)

  data cpsvalue𝑐[_] (var : cpstyp → Set) : cpstyp → Set where
    CPSVar : {τ₁ : cpstyp} → var τ₁ → cpsvalue𝑐[ var ] τ₁
    CPSNum : ℕ → cpsvalue𝑐[ var ] Nat
    CPSFun : {τ τ₀ τ₁ τ₂ τ₃ τ₄ : cpstyp} →
             (var τ₀ → var (τ₁ ⇒[ (τ₃ ⇒ τ) ]⇒ τ) → cpsterm𝑐[ var ] (τ₂ ⇒ τ₂) τ₄) →
             -- (var τ₂ → var (τ₁ ⇒[ (τ₃ ⇒ τ₃) ]⇒ τ₃) → cpsterm𝑐[ var ] (τ₃ ⇒ τ₃) τ₄) →
             cpsvalue𝑐[ var ] (τ₀ ⇒[ τ₁ ⇒ τ₃ ]⇒ τ₄)
    CPSShift : {τ₁ τ₂ τ₃ τ₄ τ₅ : cpstyp} →
               cpsvalue𝑐[ var ]
                 (((τ₁ ⇒[ τ₂ ⇒ τ₃ ]⇒ τ₃) ⇒[ τ₄ ⇒ τ₄ ]⇒ τ₅) ⇒[ τ₁ ⇒ τ₂ ]⇒ τ₅)

  data cpsterm𝑐[_] (var : cpstyp → Set) : conttyp → cpstyp → Set where
    CPSRet : {τ₁ τ₂ τ₃ : cpstyp} →
             cpscont𝑐[ var ] (τ₃ ⇒ τ₃) τ₂ (τ₁ ⇒ τ₂) →
             cpsvalue𝑐[ var ] τ₁ →
             cpsterm𝑐[ var ] (τ₃ ⇒ τ₃) τ₂
    CPSApp : {τ₁ τ₂ τ₃ τ₄ τ₅ : cpstyp} →
             cpsvalue𝑐[ var ] (τ₂ ⇒[ τ₁ ⇒ τ₃ ]⇒ τ₄) →
             cpsvalue𝑐[ var ] τ₂ →
             cpscont𝑐[ var ] (τ₅ ⇒ τ₅) τ₄ (τ₁ ⇒ τ₃) →
             cpsterm𝑐[ var ] (τ₅ ⇒ τ₅) τ₄
    CPSRetE : {τ₀ τ₁ τ₂ τ₃ : cpstyp} →
             cpscont𝑐[ var ] (τ₃ ⇒ τ₃) τ₂ (τ₁ ⇒ τ₂) →
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
    sFun  : {τ′ τ τ₀ τ₁ τ₂ τ₃ τ₄ : cpstyp} →
            {e  : var τ′ →  var τ₀ → var (τ₁ ⇒[ (τ₃ ⇒ τ) ]⇒ τ) → cpsterm𝑐[ var ] (τ₂ ⇒ τ₂) τ₄} → 
            {v  : cpsvalue𝑐[ var ] τ′} →
            {e′ : var τ₀ → var (τ₁ ⇒[ (τ₃ ⇒ τ) ]⇒ τ) → cpsterm𝑐[ var ] (τ₂ ⇒ τ₂) τ₄} → 
            ((x : var τ₀) → (k : var (τ₁ ⇒[ (τ₃ ⇒ τ) ]⇒ τ)) →
              cpsSubstV𝑐 (λ y → (e y) x k) v (e′ x k)) → 
            cpsSubstValV𝑐 (λ y → CPSFun (λ x k → (e y) x k)) v (CPSFun (λ x k → e′ x k))

  data cpsSubstV𝑐 {var : cpstyp → Set} : {τ₁ τ₂ τ₃ : cpstyp} →
                  (var τ₁ → cpsterm𝑐[ var ] (τ₃ ⇒ τ₃) τ₂) →
                  cpsvalue𝑐[ var ] τ₁ →
                  cpsterm𝑐[ var ] (τ₃ ⇒ τ₃) τ₂ → Set where
    sApp  : {τ τ₁ τ₂ τ₃ τ₄ τ₅ : cpstyp} →
            {v₁  : var τ → cpsvalue𝑐[ var ] (τ₂ ⇒[ τ₁ ⇒ τ₃ ]⇒ τ₄) } →
            {v₂  : var τ → cpsvalue𝑐[ var ] τ₂ } →
            {k₃  : var τ → cpscont𝑐[ var ] (τ₅ ⇒ τ₅) τ₄ (τ₁ ⇒ τ₃) } →
            {v   : cpsvalue𝑐[ var ] τ } →
            {v₁′ : cpsvalue𝑐[ var ] (τ₂ ⇒[ τ₁ ⇒ τ₃ ]⇒ τ₄) } →
            {v₂′ : cpsvalue𝑐[ var ] τ₂ } →
            {k₃′ : cpscont𝑐[ var ] (τ₅ ⇒ τ₅) τ₄ (τ₁ ⇒ τ₃) } →
            cpsSubstValV𝑐 (λ x → (v₁ x)) v v₁′ →
            cpsSubstValV𝑐 (λ x → (v₂ x)) v v₂′ →
            cpsSubstContV𝑐 (λ k → (k₃ k)) v k₃′ → 
            cpsSubstV𝑐 (λ x → CPSApp (v₁ x) (v₂ x) (k₃ x)) v (CPSApp v₁′ v₂′ k₃′)
    sRet  : {τ τ₁ τ₂ τ₃ : cpstyp} →
            {k₁  : var τ → cpscont𝑐[ var ] (τ₃ ⇒ τ₃) τ₂ (τ₁ ⇒ τ₂)} →
            {v₂  : var τ → cpsvalue𝑐[ var ] τ₁} →
            {v   : cpsvalue𝑐[ var ] τ} →
            {k₁′ : cpscont𝑐[ var ] (τ₃ ⇒ τ₃) τ₂ (τ₁ ⇒ τ₂)} →
            {v₂′ : cpsvalue𝑐[ var ] τ₁} →
            cpsSubstContV𝑐 k₁ v k₁′ → cpsSubstValV𝑐 v₂ v v₂′ →
            cpsSubstV𝑐 (λ x → CPSRet (k₁ x) (v₂ x)) v (CPSRet k₁′ v₂′)
    sRetE : {τ τ₀ τ₁ τ₂ τ₃ : cpstyp} →
            {k₁  : var τ → cpscont𝑐[ var ] (τ₃ ⇒ τ₃) τ₂ (τ₁ ⇒ τ₂)} →
            {e₂  : var τ → cpsterm𝑐[ var ] (τ₀ ⇒ τ₀) τ₁} →
            {v   : cpsvalue𝑐[ var ] τ} →
            {k₁′ : cpscont𝑐[ var ] (τ₃ ⇒ τ₃) τ₂ (τ₁ ⇒ τ₂)} →
            {e₂′ : cpsterm𝑐[ var ] (τ₀ ⇒ τ₀) τ₁} →
            cpsSubstContV𝑐 k₁ v k₁′ → cpsSubstV𝑐 (λ x → e₂ x) v e₂′ → 
            cpsSubstV𝑐 (λ x → CPSRetE (k₁ x) (e₂ x)) v (CPSRetE k₁′ e₂′)

  data cpsSubstContV𝑐 {var : cpstyp → Set} : {τ τ₁ τ₂ τ₃ τ₄ : cpstyp} →
                      (var τ → cpscont𝑐[ var ] (τ₃ ⇒ τ₃) τ₄ (τ₁ ⇒ τ₂)) →
                      cpsvalue𝑐[ var ] τ →
                      cpscont𝑐[ var ] (τ₃ ⇒ τ₃) τ₄ (τ₁ ⇒ τ₂) → Set where
    sKVar≠ : {τ τ₁ τ₂ τ₃ : cpstyp}
             {v : cpsvalue𝑐[ var ] τ} {k′ : var (τ₁ ⇒[ (τ₂ ⇒ τ₂) ]⇒ τ₂)} →
             cpsSubstContV𝑐 {τ₄ = τ₃} (λ _ → CPSKVar k′) v (CPSKVar k′)
    sKId   : {τ τ₁ τ₃ : cpstyp} {v : cpsvalue𝑐[ var ] τ} →
             cpsSubstContV𝑐 {τ₁ = τ₁} {τ₄ = τ₃} (λ _ → CPSId) v CPSId
    sKFun  : {τ τ₁ τ₂ τ₃ τ₄ : cpstyp} →
             {e₁ : var τ → var τ₁ → cpsterm𝑐[ var ] (τ₄ ⇒ τ₄) τ₂ } → 
             {v  : cpsvalue𝑐[ var ] τ} →
             {e₁′ : var τ₁ → cpsterm𝑐[ var ] (τ₄ ⇒ τ₄) τ₂ } → 
             ((x₁ : var τ₁) → cpsSubstV𝑐 (λ x → (e₁ x) x₁) v (e₁′ x₁)) →
             cpsSubstContV𝑐 {τ₄ = τ₃} (λ x → CPSCont (e₁ x)) v (CPSCont e₁′)


-- 値と継続の代入規則
mutual
  data cpsSubst𝑐 {var : cpstyp → Set} : {τ τ₁ τ₃ α β γ ζ : cpstyp} →
                 (var τ → var (α ⇒[ (β ⇒ ζ) ]⇒ ζ) → cpsterm𝑐[ var ] (τ₃ ⇒ τ₃) τ₁) →
                 cpsvalue𝑐[ var ] τ →
                 cpscont𝑐[ var ] (ζ ⇒ ζ) γ (α ⇒ β) → 
                 cpsterm𝑐[ var ] (τ₃ ⇒ τ₃) τ₁ → Set where

    sApp  : {τ τ₁ τ₂ τ₃ τ₄ τ₅ α β γ ζ : cpstyp} →
            {v₁  : var τ → cpsvalue𝑐[ var ] (τ₂ ⇒[ τ₁ ⇒ τ₃ ]⇒ τ₄) } →
            {v₂  : var τ → cpsvalue𝑐[ var ] τ₂ } →
            {k₃  : var τ → var (α ⇒[ (β ⇒ ζ) ]⇒ ζ) →
                   cpscont𝑐[ var ] (τ₅ ⇒ τ₅) τ₄ (τ₁ ⇒ τ₃) } →
            {v   : cpsvalue𝑐[ var ] τ } →
            {c   : cpscont𝑐[ var ] (ζ ⇒ ζ) γ (α ⇒ β) } →
            {v₁′ : cpsvalue𝑐[ var ] (τ₂ ⇒[ τ₁ ⇒ τ₃ ]⇒ τ₄) } → 
            {v₂′ : cpsvalue𝑐[ var ] τ₂ } →
            {k₃′ : cpscont𝑐[ var ] (τ₅ ⇒ τ₅) τ₄ (τ₁ ⇒ τ₃) } →
            cpsSubstValV𝑐 v₁ v v₁′ →
            cpsSubstValV𝑐 v₂ v v₂′ →
            cpsSubstCont𝑐 k₃ v c k₃′ → 
            cpsSubst𝑐 (λ x k → CPSApp (v₁ x) (v₂ x) (k₃ x k)) v c (CPSApp v₁′ v₂′ k₃′)

    sRet  : {τ τ₁ τ₂ τ₃ α β γ ζ : cpstyp} →
            {k₁  : var τ → var (α ⇒[ (β ⇒ ζ) ]⇒ ζ) →
                   cpscont𝑐[ var ] (τ₃ ⇒ τ₃) τ₂ (τ₁ ⇒ τ₂)} →
            {v₂  : var τ → cpsvalue𝑐[ var ] τ₁} →
            {v   : cpsvalue𝑐[ var ] τ} →
            {c   : cpscont𝑐[ var ] (ζ ⇒ ζ) γ (α ⇒ β)} → 
            {k₁′ : cpscont𝑐[ var ] (τ₃ ⇒ τ₃) τ₂ (τ₁ ⇒ τ₂)} →
            {v₂′ : cpsvalue𝑐[ var ] τ₁} →
            cpsSubstCont𝑐 k₁ v c k₁′ → cpsSubstValV𝑐 v₂ v v₂′ →
            cpsSubst𝑐 (λ x k → CPSRet (k₁ x k) (v₂ x)) v c (CPSRet k₁′ v₂′)

    sRetE : {τ τ₀ τ₁ τ₂ τ₃ α β γ ζ : cpstyp} →
            {k₁  : var τ → var (α ⇒[ (β ⇒ ζ) ]⇒ ζ) → cpscont𝑐[ var ] (τ₃ ⇒ τ₃) τ₂ (τ₁ ⇒ τ₂)} →
            {e₂  : var τ → var (α ⇒[ (β ⇒ ζ) ]⇒ ζ) → cpsterm𝑐[ var ] (τ₀ ⇒ τ₀) τ₁} →
            {v   : cpsvalue𝑐[ var ] τ} →
            {c   : cpscont𝑐[ var ] (ζ ⇒ ζ) γ (α ⇒ β)} → 
            {k₁′ : cpscont𝑐[ var ] (τ₃ ⇒ τ₃) τ₂ (τ₁ ⇒ τ₂)} →
            {e₂′ : cpsterm𝑐[ var ] (τ₀ ⇒ τ₀) τ₁} →
            cpsSubstCont𝑐 k₁ v c k₁′ → cpsSubst𝑐 (λ x k → e₂ x k) v c e₂′ → 
            cpsSubst𝑐 (λ x k → CPSRetE (k₁ x k) (e₂ x k)) v c (CPSRetE k₁′ e₂′)

  data cpsSubstCont𝑐 {var : cpstyp → Set} : {τ τ₁ τ₂ τ₃ τ₄ α β γ ζ : cpstyp} →
                     (var τ → var (α ⇒[ (β ⇒ ζ) ]⇒ ζ) →
                       cpscont𝑐[ var ] (τ₃ ⇒ τ₃) τ₄ (τ₁ ⇒ τ₂)) →
                     cpsvalue𝑐[ var ] τ →
                     cpscont𝑐[ var ] (ζ ⇒ ζ) γ (α ⇒ β) → 
                     cpscont𝑐[ var ] (τ₃ ⇒ τ₃) τ₄ (τ₁ ⇒ τ₂) → Set where
    sKVar= : {τ α β γ : cpstyp} {v : cpsvalue𝑐[ var ] τ}
             {c : cpscont𝑐[ var ] (β ⇒ β) γ (α ⇒ β)} →
             cpsSubstCont𝑐 (λ _ k → CPSKVar k) v c c
    sKVar≠ : {τ α β γ ζ τ₁ τ₂ τ₃ : cpstyp}
             {v : cpsvalue𝑐[ var ] τ}
             {c : cpscont𝑐[ var ] (ζ ⇒ ζ) γ (α ⇒ β)} {k′ : var (τ₁ ⇒[ (τ₂ ⇒ τ₂) ]⇒ τ₂)} →
             cpsSubstCont𝑐 {τ₄ = τ₃} (λ _ _ → CPSKVar k′) v c (CPSKVar k′)
    sKId   : {τ α β γ ζ τ₁ τ₃ : cpstyp} →
             {v : cpsvalue𝑐[ var ] τ} {c : cpscont𝑐[ var ] (ζ ⇒ ζ) γ (α ⇒ β)} →
             cpsSubstCont𝑐 {τ₁ = τ₁} {τ₄ = τ₃} (λ _ _ → CPSId) v c CPSId
    sKFun  : {τ τ₁ τ₂ τ₃ τ₄ α β γ ζ : cpstyp} →
             {e₁ : var τ → var (α ⇒[ (β ⇒ ζ) ]⇒ ζ) → var τ₁ → cpsterm𝑐[ var ] (τ₄ ⇒ τ₄) τ₂} → 
             {v  : cpsvalue𝑐[ var ] τ} → 
             {c  : cpscont𝑐[ var ] (ζ ⇒ ζ) γ (α ⇒ β)} →
             {e₁′ : var τ₁ → cpsterm𝑐[ var ] (τ₄ ⇒ τ₄) τ₂} → 
             ((x₁ : var τ₁) → cpsSubst𝑐 (λ x k → (e₁ x k) x₁) v c (e₁′ x₁)) →
             cpsSubstCont𝑐 {τ₄ = τ₃} (λ x k → CPSCont (e₁ x k)) v c (CPSCont e₁′)

data cpsReduceR {var : cpstyp → Set}  :
                {τ τ₁ τ₂ τ₃ τ₄ : cpstyp} →
                (var (τ₁ ⇒[ (τ₃ ⇒ τ) ]⇒ τ) → cpsterm𝑐[ var ] (τ₂ ⇒ τ₂) τ₄) →
                (var (τ₁ ⇒[ (τ₃ ⇒ τ) ]⇒ τ) → cpsterm𝑐[ var ] (τ₂ ⇒ τ₂) τ₄) → Set where
     βVal𝑐   : {τ′ τ₁′ τ₃′ τ₀ τ₁ τ₂ τ₃ τ₄ : cpstyp} →
               {e₁ : var τ₀ → var (τ₁ ⇒[ (τ₃ ⇒ τ₂) ]⇒ τ₂) → cpsterm𝑐[ var ] (τ₂ ⇒ τ₂) τ₄} →
               {v : cpsvalue𝑐[ var ] τ₀} →
               {c : cpscont𝑐[ var ] (τ₂ ⇒ τ₂) τ₄ (τ₁ ⇒ τ₃)} →
               {e₂ : cpsterm𝑐[ var ] (τ₂ ⇒ τ₂) τ₄} →
               cpsSubst𝑐 e₁ v c e₂ →
               cpsReduceR {τ = τ′} {τ₁ = τ₁′} {τ₃ = τ₃′}
                          (λ k → CPSApp (CPSFun (λ x k′ → e₁ x k′)) v c)
                          (λ k → e₂)

 
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

data cpsReduce• {var : cpstyp → Set} :
                {τ₁ τ₂ : cpstyp} →
                cpsterm𝑐[ var ] (τ₂ ⇒ τ₂) τ₁ →
                cpsterm𝑐[ var ] (τ₂ ⇒ τ₂) τ₁ → Set where
     βShift𝑐  : {τ₁ τ₃ τ₄ : cpstyp} →
                {w : cpsvalue𝑐[ var ] ((τ₃ ⇒[ τ₄ ⇒ τ₃ ]⇒ τ₃) ⇒[ τ₁ ⇒ τ₁ ]⇒ τ₄)} →
                {j : cpscont𝑐[ var ] (τ₁ ⇒ τ₁) τ₄ (τ₃ ⇒ τ₄)} →
                -- {w : cpsvalue𝑐[ var ] ((τ₃ ⇒[ τ₄ ⇒ τ₃ ]⇒ τ₃) ⇒[ τ₃ ⇒ τ₃ ]⇒ τ₄)} →
                -- {j : cpscont𝑐[ var ] (τ₃ ⇒ τ₃) τ₄ (τ₃ ⇒ τ₄)} →                
                cpsReduce• (CPSApp CPSShift w j)
                           (CPSApp w (CPSFun (λ x k → CPSRetE (CPSKVar k) (CPSRet j (CPSVar x)))) CPSId)

data cpsReduce𝑅 {var : cpstyp → Set} :
                {τ₂ : cpstyp} →
                cpsterm𝑐[ var ] (τ₂ ⇒ τ₂) τ₂ →
                cpsvalue𝑐[ var ] τ₂ → Set where
     βReset𝑐 : {τ₁ : cpstyp} →
               {v : cpsvalue𝑐[ var ] τ₁} →
               cpsReduce𝑅 (CPSRet CPSId v) v

data cpsReduceV {var : cpstyp → Set}  :
                 {τ₁ : cpstyp} →
                 cpsvalue𝑐[ var ] τ₁ →
                 cpsvalue𝑐[ var ] τ₁ → Set where
     ηVal𝑐 : {τ₁ τ₂ τ₃ τ₄ : cpstyp} →
             {v : cpsvalue𝑐[ var ] (τ₄ ⇒[ τ₁ ⇒ τ₃ ]⇒ τ₄)} →
             cpsReduceV (CPSFun (λ x k → CPSApp v (CPSVar x) (CPSKVar k))) v

data cpsReduceK {var : cpstyp → Set}  :
                {τ₁ τ₂ τ₃ τ₄ : cpstyp} →
                cpscont𝑐[ var ] (τ₃ ⇒ τ₃) τ₄ (τ₁ ⇒ τ₂) →
                cpscont𝑐[ var ] (τ₃ ⇒ τ₃) τ₄ (τ₁ ⇒ τ₂) → Set where
     ηLet𝑐 : {τ₁ τ₂ τ₃ : cpstyp} →
             {k : cpscont𝑐[ var ] (τ₃ ⇒ τ₃) τ₂ (τ₁ ⇒ τ₂)} →
             cpsReduceK (CPSCont (λ x → CPSRet k (CPSVar x))) k

