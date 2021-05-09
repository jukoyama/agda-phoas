module CPSterm where

open import DSterm

-- open import Data.Unit
-- open import Data.Empty
open import Data.Nat
open import Function
-- open import Relation.Binary.PropositionalEquality

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
  data cpsvalue𝑐[_,_] (var : cpstyp → Set) (cvar : conttyp → Set) : cpstyp → Set where
    CPSVar : {τ₁ : cpstyp} → var τ₁ → cpsvalue𝑐[ var , cvar ] τ₁
    CPSNum : ℕ → cpsvalue𝑐[ var , cvar ] Nat
    CPSFun : {τ₁ τ₂ τ₃ τ₄ : cpstyp} →
              (var τ₂ → cvar (τ₁ ⇒ τ₃) → cpsterm𝑐[ var , cvar ] τ₄) →
              cpsvalue𝑐[ var , cvar ] (τ₂ ⇒[ τ₁ ⇒ τ₃ ]⇒ τ₄)
    CPSShift : {τ₁ τ₂ τ₃ τ₄ τ₅ : cpstyp} →
               cpsvalue𝑐[ var , cvar ]
                 (((τ₁ ⇒[ τ₂ ⇒ τ₃ ]⇒ τ₃) ⇒[ τ₄ ⇒ τ₄ ]⇒ τ₅) ⇒[ τ₁ ⇒ τ₂ ]⇒ τ₅)

  data cpsterm𝑐[_,_] (var : cpstyp → Set) (cvar : conttyp → Set) : cpstyp → Set where
    CPSRet : {τ₁ τ₂ : cpstyp} →
             cpscont𝑐[ var , cvar ] (τ₂ ⇒ τ₁) →
             cpsvalue𝑐[ var , cvar ] τ₂ →
             cpsterm𝑐[ var , cvar ] τ₁
    CPSApp : {τ₁ τ₂ τ₃ τ₄ : cpstyp} →
             cpsvalue𝑐[ var , cvar ] (τ₂ ⇒[ τ₁ ⇒ τ₃ ]⇒ τ₄) →
             cpsvalue𝑐[ var , cvar ] τ₂ →
             cpscont𝑐[ var , cvar ] (τ₁ ⇒ τ₃) →
             cpsterm𝑐[ var , cvar ] τ₄
    CPSRetE : {τ₁ τ₂ : cpstyp} →
             cpscont𝑐[ var , cvar ] (τ₂ ⇒ τ₁) →
             cpsterm𝑐[ var , cvar ] τ₂ →
             cpsterm𝑐[ var , cvar ] τ₁


  data cpscont𝑐[_,_] (var : cpstyp → Set) (cvar : conttyp → Set) : conttyp → Set where
    CPSKVar : {τ₁ τ₂ : cpstyp} → cvar (τ₁ ⇒ τ₂) → cpscont𝑐[ var , cvar ] (τ₁ ⇒ τ₂)
    CPSId   : {τ₁ : cpstyp} → cpscont𝑐[ var , cvar ] (τ₁ ⇒ τ₁)
    CPSCont : {τ₁ τ₂ : cpstyp} → (var τ₁ → cpsterm𝑐[ var , cvar ] τ₂) →
              cpscont𝑐[ var , cvar ] (τ₁ ⇒ τ₂)
              
-- sFun と sRoot の方の書き方はあっているのか...?

-- -- 値と継続の代入規則
mutual
  data cpsSubstVal𝑐 {var : cpstyp → Set} {cvar : conttyp → Set} : {τ₁ τ₂ τ₃ τ₄ : cpstyp} →
                    (var τ₃ → cvar (τ₂ ⇒ τ₁) → cpsvalue𝑐[ var , cvar ] τ₄) →
                    cpsvalue𝑐[ var , cvar ] τ₃ →
                    cpscont𝑐[ var , cvar ] (τ₂ ⇒ τ₁) → 
                    cpsvalue𝑐[ var , cvar ] τ₄ → Set where
    sVar= : {τ₁ α β : cpstyp} {v : cpsvalue𝑐[ var , cvar ] τ₁} {c : cpscont𝑐[ var , cvar ] (α ⇒ β)} →
            cpsSubstVal𝑐 (λ x _ → CPSVar x) v c v
    sVar≠ : {τ₁ τ₂ α β : cpstyp}
            {v : cpsvalue𝑐[ var , cvar ] τ₂} {c : cpscont𝑐[ var , cvar ] (α ⇒ β)} {x : var τ₁} →
            cpsSubstVal𝑐 (λ _ _ → CPSVar x) v c (CPSVar x)
    sNum  : {τ₁ α β : cpstyp}
            {v : cpsvalue𝑐[ var , cvar ] τ₁} {c : cpscont𝑐[ var , cvar ] (α ⇒ β)} {n : ℕ} →
            cpsSubstVal𝑐 (λ _ _ → CPSNum n) v c (CPSNum n)
    sFun  : {τ₀ τ τ₁ τ₂ τ₃ τ₄ α β γ δ : cpstyp} →
            {e : var τ → cvar (α ⇒ β) → var τ₂ → cvar (γ ⇒ δ) → cpsterm𝑐[ var , cvar ] τ₄} → 
            {v : cpsvalue𝑐[ var , cvar ] τ} →
            {c : cpscont𝑐[ var , cvar ] (α ⇒ β)} →
            {e′ : var τ₂ → cvar (γ ⇒ δ) → cpsterm𝑐[ var , cvar ] τ₄} → 
            ((x : var τ₂) → (k : cvar (γ ⇒ δ)) →
              cpsSubst𝑐 (λ y k₂ → (e y k₂) x k) v c (e′ x k)) → 
            cpsSubstVal𝑐 (λ y k₂ → CPSFun (λ x k → (e y k₂) x k))
                         v c
                         (CPSFun (λ x k → e′ x k))

  data cpsSubst𝑐 {var : cpstyp → Set} {cvar : conttyp → Set} : {τ₁ τ₂ τ₃ τ₄ : cpstyp} →
                 (var τ₃ → cvar (τ₂ ⇒ τ₁) → cpsterm𝑐[ var , cvar ] τ₄) →
                 cpsvalue𝑐[ var , cvar ] τ₃ →
                 cpscont𝑐[ var , cvar ] (τ₂ ⇒ τ₁) → 
                 cpsterm𝑐[ var , cvar ] τ₄ → Set where
    sApp  : {τ τ₁ τ₂ τ₃ τ₄ τ₅ τ₆ τ₇ : cpstyp} →
            {v₁  : var τ₃ → cvar (τ₂ ⇒ τ₁) → cpsvalue𝑐[ var , cvar ] (τ₅ ⇒[ τ₄ ⇒ τ₆ ]⇒ τ₇) } →
            {v₂  : var τ₃ → cvar (τ₂ ⇒ τ₁) → cpsvalue𝑐[ var , cvar ] τ₅ } →
            {k₃  : var τ₃ → cvar (τ₂ ⇒ τ₁) → cpscont𝑐[ var , cvar ] (τ₄ ⇒ τ₆) } →
            {v   : cpsvalue𝑐[ var , cvar ] τ₃ } →
            {c   : cpscont𝑐[ var , cvar ] (τ₂ ⇒ τ₁) } → 
            {v₁′ : cpsvalue𝑐[ var , cvar ] (τ₅ ⇒[ τ₄ ⇒ τ₆ ]⇒ τ₇) } →
            {v₂′ : cpsvalue𝑐[ var , cvar ] τ₅ } →
            {k₃′ : cpscont𝑐[ var , cvar ] (τ₄ ⇒ τ₆) } →
            cpsSubstVal𝑐 (λ x → (v₁ x)) v c v₁′ →
            cpsSubstVal𝑐 (λ x → (v₂ x)) v c v₂′ →
            cpsSubstCont𝑐 (λ k → (k₃ k)) v c k₃′ → 
            cpsSubst𝑐 (λ x k → CPSApp (v₁ x k) (v₂ x k) (k₃ x k)) v c (CPSApp v₁′ v₂′ k₃′)           
    sRet  : {τ τ₁ τ₂ τ₃ τ₄ τ₅ : cpstyp} →
            {k₁  : var τ₃ → cvar (τ₄ ⇒ τ₅) → cpscont𝑐[ var , cvar ] (τ₂ ⇒ τ₁)} →
            {v₂  : var τ₃ → cvar (τ₄ ⇒ τ₅) → cpsvalue𝑐[ var , cvar ] τ₂} →
            {v   : cpsvalue𝑐[ var , cvar ] τ₃} →
            {c   : cpscont𝑐[ var , cvar ] (τ₄ ⇒ τ₅)} → 
            {k₁′ : cpscont𝑐[ var , cvar ] (τ₂ ⇒ τ₁)} →
            {v₂′ : cpsvalue𝑐[ var , cvar ] τ₂} →
            cpsSubstCont𝑐 k₁ v c k₁′ → cpsSubstVal𝑐 v₂ v c v₂′ →
            cpsSubst𝑐 (λ x k → CPSRet (k₁ x k) (v₂ x k)) v c (CPSRet k₁′ v₂′)
    sRetE : {τ τ₁ τ₂ τ₃ τ₄ : cpstyp} →
            {k₁  : var τ → cvar (τ₃ ⇒ τ₄) → cpscont𝑐[ var , cvar ] (τ₂ ⇒ τ₁)} →
            {e₂  : var τ → cvar (τ₃ ⇒ τ₄) → cpsterm𝑐[ var , cvar ] τ₂} →
            {v   : cpsvalue𝑐[ var , cvar ] τ} →
            {c   : cpscont𝑐[ var , cvar ] (τ₃ ⇒ τ₄)} → 
            {k₁′ : cpscont𝑐[ var , cvar ] (τ₂ ⇒ τ₁)} →
            {e₂′ : cpsterm𝑐[ var , cvar ] τ₂} →
            cpsSubstCont𝑐 k₁ v c k₁′ → cpsSubst𝑐 (λ x k → e₂ x k) v c e₂′ → 
            cpsSubst𝑐 (λ x k → CPSRetE (k₁ x k) (e₂ x k)) v c (CPSRetE k₁′ e₂′)
  
  data cpsSubstCont𝑐 {var : cpstyp → Set} {cvar : conttyp → Set} : {τ₁ τ₂ τ₃ τ₄ τ₅ : cpstyp} →
                     (var τ₃ → cvar (τ₂ ⇒ τ₁) → cpscont𝑐[ var , cvar ] (τ₄ ⇒ τ₅)) →
                     cpsvalue𝑐[ var , cvar ] τ₃ →
                     cpscont𝑐[ var , cvar ] (τ₂ ⇒ τ₁) → 
                     cpscont𝑐[ var , cvar ] (τ₄ ⇒ τ₅) → Set where
    sKVar= : {τ₁ α β : cpstyp} {v : cpsvalue𝑐[ var , cvar ] τ₁} {c : cpscont𝑐[ var , cvar ] (α ⇒ β)} →
             cpsSubstCont𝑐 (λ _ k → CPSKVar k) v c c
    sKVar≠ : {τ₁ τ₂ τ₃ τ₄ α β : cpstyp}
             -- ここの型はあっているのか ...?
             {v : cpsvalue𝑐[ var , cvar ] τ₁} {c : cpscont𝑐[ var , cvar ] (α ⇒ β)} {k : cvar (α ⇒ β)} →
             cpsSubstCont𝑐 (λ _ k → CPSKVar k) v c (CPSKVar k)
    sKFun  : {τ₀ τ τ₁ τ₂ τ₃ τ₄ τ₅ : cpstyp} →
             {e₁ : var τ₅ → cvar (τ₁ ⇒ τ₂) → var τ₃ → cpsterm𝑐[ var , cvar ] τ₄ } → 
             {v  : cpsvalue𝑐[ var , cvar ] τ₅} → 
             {c  : cpscont𝑐[ var , cvar ] (τ₁ ⇒ τ₂)} →
             {e₁′ : var τ₃ → cpsterm𝑐[ var , cvar ] τ₄ } → 
             ((x₁ : var τ₃) → cpsSubst𝑐 (λ x k → (e₁ x k) x₁) v c (e₁′ x₁)) →
             cpsSubstCont𝑐 (λ x k → CPSCont (e₁ x k)) v c (CPSCont e₁′)

-- 値による代入規則
mutual
  data cpsSubstValK𝑐 {var : cpstyp → Set} {cvar : conttyp → Set} : {τ₁ τ₂ : cpstyp} →
                    (var τ₁ → cpsvalue𝑐[ var , cvar ] τ₂) →
                    cpsvalue𝑐[ var , cvar ] τ₁ →
                    cpsvalue𝑐[ var , cvar ] τ₂ → Set where
    sVar= : {τ₁ : cpstyp} {v : cpsvalue𝑐[ var , cvar ] τ₁} →
            cpsSubstValK𝑐 (λ x → CPSVar x) v v
    sVar≠ : {τ₁ τ₂ : cpstyp} {v : cpsvalue𝑐[ var , cvar ] τ₂} {x : var τ₁} →
            cpsSubstValK𝑐 (λ _ → CPSVar x) v (CPSVar x)
    sNum  : {τ₁ : cpstyp} {v : cpsvalue𝑐[ var , cvar ] τ₁}  {n : ℕ} →
            cpsSubstValK𝑐 (λ _ → CPSNum n) v (CPSNum n)
    sFun  : {τ τ₂ τ₄ γ δ : cpstyp} →
            {e  : var τ →  var τ₂ → cvar (γ ⇒ δ) → cpsterm𝑐[ var , cvar ] τ₄} → 
            {v  : cpsvalue𝑐[ var , cvar ] τ} →
            {e′ : var τ₂ → cvar (γ ⇒ δ) → cpsterm𝑐[ var , cvar ] τ₄} → 
            ((x : var τ₂) → (k : cvar (γ ⇒ δ)) →
              cpsSubstK𝑐 (λ y → (e y) x k) v (e′ x k)) → 
            cpsSubstValK𝑐 (λ y → CPSFun (λ x k → (e y) x k)) v (CPSFun (λ x k → e′ x k))
            
  data cpsSubstK𝑐 {var : cpstyp → Set} {cvar : conttyp → Set} : {τ₁ τ₂ : cpstyp} →
                  (var τ₁ → cpsterm𝑐[ var , cvar ] τ₂) →
                  cpsvalue𝑐[ var , cvar ] τ₁ →
                  cpsterm𝑐[ var , cvar ] τ₂ → Set where
    sApp  : {τ₁ τ₂ τ₃ τ₄ τ₅ τ₆ τ₇ : cpstyp} →
            {v₁  : var τ₃ → cpsvalue𝑐[ var , cvar ] (τ₅ ⇒[ τ₄ ⇒ τ₆ ]⇒ τ₇) } →
            {v₂  : var τ₃ → cpsvalue𝑐[ var , cvar ] τ₅ } →
            {k₃  : var τ₃ → cpscont𝑐[ var , cvar ] (τ₄ ⇒ τ₆) } →
            {v   : cpsvalue𝑐[ var , cvar ] τ₃ } →
            {v₁′ : cpsvalue𝑐[ var , cvar ] (τ₅ ⇒[ τ₄ ⇒ τ₆ ]⇒ τ₇) } →
            {v₂′ : cpsvalue𝑐[ var , cvar ] τ₅ } →
            {k₃′ : cpscont𝑐[ var , cvar ] (τ₄ ⇒ τ₆) } →
            cpsSubstValK𝑐 (λ x → (v₁ x)) v v₁′ →
            cpsSubstValK𝑐 (λ x → (v₂ x)) v v₂′ →
            cpsSubstContK𝑐 (λ k → (k₃ k)) v k₃′ → 
            cpsSubstK𝑐 (λ x → CPSApp (v₁ x) (v₂ x) (k₃ x)) v (CPSApp v₁′ v₂′ k₃′)           
    sRet  : {τ τ₁ τ₂ τ₃ : cpstyp} →
            {k₁  : var τ₃ → cpscont𝑐[ var , cvar ] (τ₂ ⇒ τ₁)} →
            {v₂  : var τ₃ → cpsvalue𝑐[ var , cvar ] τ₂} →
            {v   : cpsvalue𝑐[ var , cvar ] τ₃} →
            {k₁′ : cpscont𝑐[ var , cvar ] (τ₂ ⇒ τ₁)} →
            {v₂′ : cpsvalue𝑐[ var , cvar ] τ₂} →
            cpsSubstContK𝑐 k₁ v k₁′ → cpsSubstValK𝑐 v₂ v v₂′ →
            cpsSubstK𝑐 (λ x → CPSRet (k₁ x) (v₂ x)) v (CPSRet k₁′ v₂′)
    sRetE : {τ τ₁ τ₂ : cpstyp} →
            {k₁  : var τ → cpscont𝑐[ var , cvar ] (τ₂ ⇒ τ₁)} →
            {e₂  : var τ → cpsterm𝑐[ var , cvar ] τ₂} →
            {v   : cpsvalue𝑐[ var , cvar ] τ} →
            {k₁′ : cpscont𝑐[ var , cvar ] (τ₂ ⇒ τ₁)} →
            {e₂′ : cpsterm𝑐[ var , cvar ] τ₂} →
            cpsSubstContK𝑐 k₁ v k₁′ → cpsSubstK𝑐 (λ x → e₂ x) v e₂′ → 
            cpsSubstK𝑐 (λ x → CPSRetE (k₁ x) (e₂ x)) v (CPSRetE k₁′ e₂′)

  data cpsSubstContK𝑐 {var : cpstyp → Set} {cvar : conttyp → Set} : {τ₁ τ₂ τ₃ : cpstyp} →
                      (var τ₁ → cpscont𝑐[ var , cvar ] (τ₂ ⇒ τ₃)) →
                      cpsvalue𝑐[ var , cvar ] τ₁ →
                      cpscont𝑐[ var , cvar ] (τ₂ ⇒ τ₃) → Set where
    sKVar≠ : {τ₁ α β : cpstyp}
             {v : cpsvalue𝑐[ var , cvar ] τ₁} {k : cvar (α ⇒ β)} →
             cpsSubstContK𝑐 (λ _ → CPSKVar k) v (CPSKVar k)
    sKFun  : {τ₀ τ τ₁ τ₂ τ₃ τ₄ τ₅ : cpstyp} →
             {e₁ : var τ₅ → var τ₃ → cpsterm𝑐[ var , cvar ] τ₄ } → 
             {v  : cpsvalue𝑐[ var , cvar ] τ₅} → 
             {e₁′ : var τ₃ → cpsterm𝑐[ var , cvar ] τ₄ } → 
             ((x₁ : var τ₃) → cpsSubstK𝑐 (λ x → (e₁ x) x₁) v (e₁′ x₁)) →
             cpsSubstContK𝑐 (λ x → CPSCont (e₁ x)) v (CPSCont e₁′)


mutual 
  data cpsReduce {var : cpstyp → Set} {cvar : conttyp → Set} :
                 {τ₁ : cpstyp} →
                 cpsterm𝑐[ var , cvar ] τ₁ →
                 cpsterm𝑐[ var , cvar ] τ₁ → Set where
       RBeta𝑐   : {τ₁ τ₂ τ₃ τ₄ : cpstyp} →
                  {e₁ : var τ₂ → cvar (τ₁ ⇒ τ₃) → cpsterm𝑐[ var , cvar ] τ₄} →
                  {v : cpsvalue𝑐[ var , cvar ] τ₂} →
                  {c : cpscont𝑐[ var , cvar ] (τ₁ ⇒ τ₃)} →
                  {e₂ : cpsterm𝑐[ var , cvar ] τ₄} →
                  cpsSubst𝑐 e₁ v c e₂ →
                  cpsReduce (CPSApp (CPSFun (λ x k → e₁ x k)) v c) e₂
       RLet𝑐    : {τ₁ τ₂ : cpstyp} →
                  {v₁ : cpsvalue𝑐[ var , cvar ] τ₁} →
                  {e𝑐 : var τ₁ → cpsterm𝑐[ var , cvar ] τ₂} →
                  {e𝑐′ : cpsterm𝑐[ var , cvar ] τ₂} →
                  cpsSubstK𝑐 e𝑐 v₁ e𝑐′ → 
                  cpsReduce (CPSRet (CPSCont (λ x → e𝑐 x)) v₁) e𝑐′
       RShift𝑐  : {τ₁ τ₂ τ₃ τ₄ τ₅ : cpstyp} →
                  -- CPSId の書き方はこれでいいのか
                  {v₂ : cpsvalue𝑐[ var , cvar ] ((τ₁ ⇒[ τ₂ ⇒ τ₃ ]⇒ τ₃) ⇒[ τ₄ ⇒ τ₄ ]⇒ τ₅)} →
                  {c₃ : cpscont𝑐[ var , cvar ] (τ₁ ⇒ τ₂)} →
                  cpsReduce (CPSApp CPSShift v₂ c₃)
                            (CPSApp v₂
                                    (CPSFun (λ x k → CPSRetE (CPSKVar k) (CPSRet c₃ (CPSVar x))))
                                    CPSId)
       -- RReset   : {τ₁ τ₂ : cpstyp} →
       --            {v₂ : cpsvalue𝑐[ var , cvar ] {!!}} →
       --            -- cpsReduce (CPSRet (CPSId (λ x → CPSVar x)) {!!}) {!v₂!}
       RId𝑐     : {τ₁ : cpstyp} →
                  {e : cpsterm𝑐[ var , cvar ] τ₁} →
                  cpsReduce e e
       RTrans𝑐  : {τ₁ : cpstyp} →
                  (e₁ e₂ e₃ : cpsterm𝑐[ var , cvar ] τ₁) →
                  cpsReduce e₁ e₂ →
                  cpsReduce e₂ e₃ →
                  cpsReduce e₁ e₃
       RTrans𝑐′ : {τ₁ : cpstyp} →
                  (e₁ e₂ e₃ : cpsterm𝑐[ var , cvar ] τ₁) →
                  cpsReduce e₂ e₁ →
                  cpsReduce e₂ e₃ →
                  cpsReduce e₁ e₃
