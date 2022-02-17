module Lemma_DS_Subst where

open import CPSterm
open import DStermK
open import DSTrans

open import Function

mutual
  eSubstValV𝑘 : {var : typ𝑘 → Set} {cvar : typ𝑘𝑐 → Set} {τ₁ τ : cpstyp} →
                {v₁ : var (dsT τ) → cpsvalue𝑐[ var ∘ dsT , cvar ∘ dsT𝑐 ] τ₁} →
                {v₂ : cpsvalue𝑐[ var ∘ dsT , cvar ∘ dsT𝑐 ] τ₁} →
                {v  : cpsvalue𝑐[ var ∘ dsT , cvar ∘ dsT𝑐 ] τ} →
                cpsSubstValV𝑐 v₁ v v₂ →
                SubstValV𝑘 {var} {cvar}
                           (λ y → dsV𝑐 (v₁ y)) (dsV𝑐 v)
                           (dsV𝑐 v₂)
  eSubstValV𝑘 sVar=  = sVar=
  eSubstValV𝑘 sVar≠  = sVar≠
  eSubstValV𝑘 sNum   = sNum
  eSubstValV𝑘 sShift = sShift
  eSubstValV𝑘 (sFun sub) =
    sFun (λ x k → eSubstV𝑘 (sub x k))

  eSubstConV𝑘 : {var : typ𝑘 → Set} {cvar : typ𝑘𝑐 → Set} {τ τ₁ τ₂ : cpstyp} →
                {k₁ : var (dsT τ) →
                      cpscont𝑐[ var ∘ dsT , cvar ∘ dsT𝑐 ] (τ₁ ⇒ τ₂)} →
                {k₂ : cpscont𝑐[ var ∘ dsT , cvar ∘ dsT𝑐 ] (τ₁ ⇒ τ₂)} →
                {v  : cpsvalue𝑐[ var ∘ dsT , cvar ∘ dsT𝑐 ] τ} →
                cpsSubstContV𝑐 k₁ v k₂ →
                SubstConV𝑘 {var} {cvar}
                           (λ y → dsC𝑐 (k₁ y))
                           (dsV𝑐 v) (dsC𝑐 k₂)
  eSubstConV𝑘 sKVar≠      = sConVar≠
  eSubstConV𝑘 sKId        = sConId
  eSubstConV𝑘 (sKFun sub) = sConLet (λ x → eSubstV𝑘 (sub x))

  eSubstV𝑘 : {var : typ𝑘 → Set} {cvar : typ𝑘𝑐 → Set} {τ τ₁ : cpstyp} →
             {e₁ : var (dsT τ) →
                   cpsterm𝑐[ var ∘ dsT , cvar ∘ dsT𝑐 ] τ₁} →
             {e₂ : cpsterm𝑐[ var ∘ dsT , cvar ∘ dsT𝑐 ] τ₁} →
             {v  : cpsvalue𝑐[ var ∘ dsT , cvar ∘ dsT𝑐 ] τ} →
             cpsSubstV𝑐 e₁ v e₂ →
             SubstV𝑘 {var} {cvar}
                     (λ y → dsE𝑐 (e₁ y))
                     (dsV𝑐 v) (dsE𝑐 e₂)
  eSubstV𝑘 (sApp sub-v sub-w sub-k) = sApp (eSubstConV𝑘 sub-k)
                                           (eSubstValV𝑘 sub-v)
                                           (eSubstValV𝑘 sub-w)
  eSubstV𝑘 (sRet sub-k sub-v)       = sVal (eSubstConV𝑘 sub-k)
                                           (eSubstValV𝑘 sub-v)
  eSubstV𝑘 (sRetE sub-k sub-e)      = sReset (eSubstConV𝑘 sub-k)
                                             (eSubstV𝑘 sub-e)

mutual
  eSubstConVK𝑘 : {var : typ𝑘 → Set} {cvar : typ𝑘𝑐 → Set}
                 {τ τ₁ τ₂ α β : cpstyp} →
                 {k₁ : var (dsT τ) → cvar (dsT𝑐 (α ⇒ β)) →
                       cpscont𝑐[ var ∘ dsT , cvar ∘ dsT𝑐 ] (τ₁ ⇒ τ₂)} →
                 {k₂ : cpscont𝑐[ var ∘ dsT , cvar ∘ dsT𝑐 ] (τ₁ ⇒ τ₂)} →
                 {v  : cpsvalue𝑐[ var ∘ dsT , cvar ∘ dsT𝑐 ] τ} →
                 {c : cpscont𝑐[ var ∘ dsT , cvar ∘ dsT𝑐 ] (α ⇒ β)} →
                 cpsSubstCont𝑐 k₁ v c k₂ →
                 SubstCon𝑘 {var} {cvar}
                 (λ y k′ → dsC𝑐 (k₁ y k′))
                 (dsV𝑐 v) (dsC𝑐 c)
                 (dsC𝑐 k₂)
  eSubstConVK𝑘 sKVar=      = sCon=
  eSubstConVK𝑘 sKVar≠      = sCon≠
  eSubstConVK𝑘 sKId        = sHole
  eSubstConVK𝑘 (sKFun sub) = sLet (λ x → eSubstVK𝑘 (sub x))
  
  eSubstVK𝑘 : {var : typ𝑘 → Set} {cvar : typ𝑘𝑐 → Set} {τ τ₁ α β : cpstyp} →
              {e₁ : var (dsT τ) → cvar (dsT𝑐 (α ⇒ β)) →
                    cpsterm𝑐[ var ∘ dsT , cvar ∘ dsT𝑐 ] τ₁} →
              {e₂ : cpsterm𝑐[ var ∘ dsT , cvar ∘ dsT𝑐 ] τ₁} →
              {v  : cpsvalue𝑐[ var ∘ dsT , cvar ∘ dsT𝑐 ] τ} →
              {c : cpscont𝑐[ var ∘ dsT , cvar ∘ dsT𝑐 ] (α ⇒ β)} →
              cpsSubst𝑐 e₁ v c e₂ → 
              Subst𝑘 {var} {cvar}
                     (λ y k′ → dsE𝑐 (e₁ y k′))
                     (dsV𝑐 v) (dsC𝑐 c)
                     (dsE𝑐 e₂)
  eSubstVK𝑘 (sApp sub-v sub-w sub-k) = sApp (eSubstConVK𝑘 sub-k)
                                            (eSubstValV𝑘 sub-v)
                                            (eSubstValV𝑘 sub-w)
  eSubstVK𝑘 (sRet sub-k sub-v)       = sVal (eSubstConVK𝑘 sub-k)
                                            (eSubstValV𝑘 sub-v)
  eSubstVK𝑘 (sRetE sub-k sub-e)      = sReset (eSubstConVK𝑘 sub-k)
                                              (eSubstVK𝑘 sub-e)

