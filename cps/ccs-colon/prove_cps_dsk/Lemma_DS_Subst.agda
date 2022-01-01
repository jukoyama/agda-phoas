module Lemma_DS_Subst where

open import CPSterm
open import DStermK
open import DSTrans

open import Function

mutual
  eSubstValV𝑘 : {var : typ𝑘 → Set} {τ₁ τ : cpstyp} →
                {v₁ : var (dsT τ) → cpsvalue𝑐[ var ∘ dsT ] τ₁} →
                {v₂ : cpsvalue𝑐[ var ∘ dsT ] τ₁} →
                {v  : cpsvalue𝑐[ var ∘ dsT ] τ} →
                cpsSubstValV𝑐 v₁ v v₂ →
                SubstValV𝑘 {var} (λ y → dsV𝑐 τ₁ (v₁ y))
                                 (dsV𝑐 τ v)
                                 (dsV𝑐 τ₁ v₂)
  eSubstValV𝑘 sVar=  = sVar=
  eSubstValV𝑘 sVar≠  = sVar≠
  eSubstValV𝑘 sNum   = sNum
  eSubstValV𝑘 sShift = sShift
  eSubstValV𝑘 (sFun sub) =
    sFun (λ x k → eSubstV𝑘 (sub x k))

  eSubstConV𝑘 : {var : typ𝑘 → Set} {τ τ₁ τ₂ τ₃ τ₄ : cpstyp} →
                {k₁ : var (dsT τ) →
                      cpscont𝑐[ var ∘ dsT ] (τ₄ ⇒ τ₄) τ₃ (τ₁ ⇒ τ₂)} →
                {k₂ : cpscont𝑐[ var ∘ dsT ] (τ₄ ⇒ τ₄) τ₃ (τ₁ ⇒ τ₂)} →
                {v  : cpsvalue𝑐[ var ∘ dsT ] τ} →
                cpsSubstContV𝑐 k₁ v k₂ →
                SubstConV𝑘 {var} (λ y → dsC𝑐 τ₁ τ₂ τ₃ τ₄ (k₁ y))
                                 (dsV𝑐 τ v)
                                 (dsC𝑐 τ₁ τ₂ τ₃ τ₄ k₂)
  eSubstConV𝑘 sKVar≠      = sConVar≠
  eSubstConV𝑘 sKId        = sConId
  eSubstConV𝑘 (sKFun sub) = sConLet (λ x → eSubstV𝑘 (sub x))

  -- eSubstRootV𝑘 : {var : typ𝑘 → Set} {τ τ₁ τ₂ τ₃ : cpstyp} →
  --                {e₁ : var (dsT τ) → var (dsT (τ₁ ⇒[ τ₂ ⇒ τ₂ ]⇒ τ₂)) → 
  --                      cpsterm𝑐[ var ∘ dsT ] (τ₂ ⇒ τ₂) τ₃} →
  --                {e₂ : var (dsT (τ₁ ⇒[ τ₂ ⇒ τ₂ ]⇒ τ₂)) →
  --                      cpsterm𝑐[ var ∘ dsT ] (τ₂ ⇒ τ₂) τ₃} →
  --                {v  : cpsvalue𝑐[ var ∘ dsT ] τ} →
  --                ((k : var (dsT (τ₁ ⇒[ τ₂ ⇒ τ₂ ]⇒ τ₂))) →
  --                      cpsSubstV𝑐 (λ x → (e₁ x) k) v (e₂ k)) → 
  --                SubstRootV𝑘 {var} (λ y → dsMain𝑐 τ₁ τ₂ τ₃ (e₁ y))
  --                                  (dsV𝑐 τ v)
  --                                  (dsMain𝑐 τ₁ τ₂ τ₃ e₂)
  -- eSubstRootV𝑘 sub = sRoot (λ k → eSubstV𝑘 (sub k))


  eSubstV𝑘 : {var : typ𝑘 → Set} {τ τ₂ τ₃ : cpstyp} →
             {e₁ : var (dsT τ) →
                   cpsterm𝑐[ var ∘ dsT ] (τ₃ ⇒ τ₃) τ₂} →
             {e₂ : cpsterm𝑐[ var ∘ dsT ] (τ₃ ⇒ τ₃) τ₂} →
             {v  : cpsvalue𝑐[ var ∘ dsT ] τ} →
             cpsSubstV𝑐 e₁ v e₂ →
             SubstV𝑘 {var} (λ y → dsE𝑐 τ₂ τ₃ (e₁ y))
                           (dsV𝑐 τ v)
                           (dsE𝑐 τ₂ τ₃ e₂)
  eSubstV𝑘 (sApp sub-v sub-w sub-k) = sApp (eSubstConV𝑘 sub-k)
                                           (eSubstValV𝑘 sub-v)
                                           (eSubstValV𝑘 sub-w)
  eSubstV𝑘 (sRet sub-k sub-v)       = sVal (eSubstConV𝑘 sub-k)
                                           (eSubstValV𝑘 sub-v)
  eSubstV𝑘 (sRetE sub-k sub-e)      = sReset (eSubstConV𝑘 sub-k)
                                             (eSubstV𝑘 sub-e)

mutual
  eSubstConVK𝑘 : {var : typ𝑘 → Set} {τ τ₁ τ₂ τ₃ τ₇ α β γ ζ : cpstyp} →
                 {k₁ : var (dsT τ) → var (dsT (α ⇒[ (β ⇒ ζ) ]⇒ ζ)) →
                       cpscont𝑐[ var ∘ dsT ] (τ₇ ⇒ τ₇) τ₃ (τ₁ ⇒ τ₂)} →
                 {k₂ : cpscont𝑐[ var ∘ dsT ] (τ₇ ⇒ τ₇) τ₃ (τ₁ ⇒ τ₂)} →
                 {v  : cpsvalue𝑐[ var ∘ dsT ] τ} →
                 {c : cpscont𝑐[ var ∘ dsT ] (ζ ⇒ ζ) γ (α ⇒ β)} →
                 cpsSubstCont𝑐 k₁ v c k₂ →
                 SubstCon𝑘 {var} (λ y k′ → dsC𝑐 τ₁ τ₂ τ₃ τ₇ (k₁ y k′))
                                 (dsV𝑐 τ v) (dsC𝑐 α β γ ζ c)
                                 (dsC𝑐 τ₁ τ₂ τ₃ τ₇ k₂)
  eSubstConVK𝑘 sKVar=      = sCon=
  eSubstConVK𝑘 sKVar≠      = sCon≠
  eSubstConVK𝑘 sKId        = sHole
  eSubstConVK𝑘 (sKFun sub) = sLet (λ x → eSubstVK𝑘 (sub x))
  
  eSubstVK𝑘 : {var : typ𝑘 → Set} {τ τ₁ τ₃ α β γ ζ  : cpstyp} →
              {e₁ : var (dsT τ) → var (dsT (α ⇒[ (β ⇒ ζ) ]⇒ ζ)) →
                    cpsterm𝑐[ var ∘ dsT ] (τ₃ ⇒ τ₃) τ₁} →
              {e₂ : cpsterm𝑐[ var ∘ dsT ] (τ₃ ⇒ τ₃) τ₁} →
              {v  : cpsvalue𝑐[ var ∘ dsT ] τ} →
              {c : cpscont𝑐[ var ∘ dsT ] (ζ ⇒ ζ) γ (α ⇒ β)} →
              cpsSubst𝑐 e₁ v c e₂ → 
              Subst𝑘 {var} (λ y k′ → dsE𝑐 τ₁ τ₃ (e₁ y k′))
                           (dsV𝑐 τ v) (dsC𝑐 α β γ ζ c)
                           (dsE𝑐 τ₁ τ₃ e₂)
  eSubstVK𝑘 (sApp sub-v sub-w sub-k) = sApp (eSubstConVK𝑘 sub-k)
                                            (eSubstValV𝑘 sub-v)
                                            (eSubstValV𝑘 sub-w)
  eSubstVK𝑘 (sRet sub-k sub-v)       = sVal (eSubstConVK𝑘 sub-k)
                                            (eSubstValV𝑘 sub-v)
  eSubstVK𝑘 (sRetE sub-k sub-e)      = sReset (eSubstConVK𝑘 sub-k)
                                              (eSubstVK𝑘 sub-e)

