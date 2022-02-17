module Lemma_CPS_Subst where

open import CPSterm
open import DStermK
open import CPSIsm

open import Function
open import Relation.Binary.PropositionalEquality

mutual
  SubstValV𝑐 : {var : cpstyp → Set} {cvar : conttyp → Set} {τ₁ τ : typ𝑘} →
               {v₁ : var (cpsT𝑘 τ) → value𝑘[ var ∘ cpsT𝑘 , cvar ∘ cpsT𝑘𝑐 ] τ₁ cps[τ,τ]} →
               {v₂ : value𝑘[ var ∘ cpsT𝑘 , cvar ∘ cpsT𝑘𝑐 ] τ₁ cps[τ,τ]} →
               {v  : value𝑘[ var ∘ cpsT𝑘 , cvar ∘ cpsT𝑘𝑐 ] τ cps[τ,τ]} →
               SubstValV𝑘 v₁ v v₂ →
               cpsSubstValV𝑐 {var} {cvar}
                             (λ y → cpsV𝑘 (v₁ y))
                             (cpsV𝑘 v)
                             (cpsV𝑘 v₂)
  SubstValV𝑐 SubstValV𝑘.sVar= = cpsSubstValV𝑐.sVar=
  SubstValV𝑐 SubstValV𝑘.sVar≠ = cpsSubstValV𝑐.sVar≠
  SubstValV𝑐 SubstValV𝑘.sNum  = cpsSubstValV𝑐.sNum
  SubstValV𝑐 SubstValV𝑘.sShift = cpsSubstValV𝑐.sShift
  SubstValV𝑐 (SubstValV𝑘.sFun sub) =
    sFun (λ x k → SubstV𝑐 (sub x k))

  SubstConV𝑐 : {var : cpstyp → Set} {cvar : conttyp → Set} {τ τ₁ τ₂ : typ𝑘} →
               {k₁ : var (cpsT𝑘 τ) → pcontext𝑘[ var ∘ cpsT𝑘 , cvar ∘ cpsT𝑘𝑐 ] (τ₁ ▷ τ₂)} →
               {k₂ : pcontext𝑘[ var ∘ cpsT𝑘  , cvar ∘ cpsT𝑘𝑐 ] (τ₁ ▷ τ₂)} →
               {v  : value𝑘[ var ∘ cpsT𝑘 , cvar ∘ cpsT𝑘𝑐 ] τ cps[τ,τ]} →
               SubstConV𝑘 k₁ v k₂ →
               cpsSubstContV𝑐 {var} {cvar}
                              (λ y → cpsC𝑘 (k₁ y))
                              (cpsV𝑘 v)
                              (cpsC𝑘 k₂)
  SubstConV𝑐 sConVar≠        = sKVar≠
  SubstConV𝑐 sConId          = sKId
  SubstConV𝑐 (sConLet sub-e) = sKFun (λ x → SubstV𝑐 (sub-e x))

  SubstV𝑐 : {var : cpstyp → Set} {cvar : conttyp → Set} {τ τ₁ : typ𝑘} →
            {e₁ : var (cpsT𝑘 τ) →
                  term𝑘[ var ∘ cpsT𝑘 , cvar ∘ cpsT𝑘𝑐 ] τ₁} →
            {e₂ : term𝑘[ var ∘ cpsT𝑘 , cvar ∘ cpsT𝑘𝑐 ] τ₁} →
            {v  : value𝑘[ var ∘ cpsT𝑘 , cvar ∘ cpsT𝑘𝑐 ] τ cps[τ,τ]} →
            SubstV𝑘 e₁ v e₂ →
            cpsSubstV𝑐 {var} {cvar} (λ y → cpsE𝑘 (e₁ y))
                             (cpsV𝑘 v)
                             (cpsE𝑘 e₂)
  SubstV𝑐 (sVal sub-k sub-v)       = sRet (SubstConV𝑐 sub-k) (SubstValV𝑐 sub-v)
  SubstV𝑐 (sApp sub-k sub-v sub-w) = sApp (SubstValV𝑐 sub-v) (SubstValV𝑐 sub-w) (SubstConV𝑐 sub-k)
  SubstV𝑐 (sReset sub-k sub-e)     = sRetE (SubstConV𝑐 sub-k) (SubstV𝑐 sub-e)

mutual
  SubstConVK𝑐 : {var : cpstyp → Set} {cvar : conttyp → Set} {τ τ₁ τ₂ α β : typ𝑘} →
                {k₁ : var (cpsT𝑘 τ) → cvar (cpsT𝑘𝑐 (α ▷ β)) → 
                      pcontext𝑘[ var ∘ cpsT𝑘 , cvar ∘ cpsT𝑘𝑐 ] (τ₁ ▷ τ₂)} →
                {k₂ : pcontext𝑘[ var ∘ cpsT𝑘  , cvar ∘ cpsT𝑘𝑐 ] (τ₁ ▷ τ₂)} →
                {v  : value𝑘[ var ∘ cpsT𝑘 , cvar ∘ cpsT𝑘𝑐 ] τ cps[τ,τ]} →
                {K𝑐 : pcontext𝑘[ var ∘ cpsT𝑘 , cvar ∘ cpsT𝑘𝑐 ] (α ▷ β)} → 
                SubstCon𝑘 k₁ v K𝑐 k₂ →
                cpsSubstCont𝑐 {var} {cvar} (λ y k′ → cpsC𝑘 (k₁ y k′))
                                    (cpsV𝑘 v)
                                    (cpsC𝑘 K𝑐)
                                    (cpsC𝑘 k₂)
  SubstConVK𝑐 sCon= = sKVar=
  SubstConVK𝑐 sCon≠ = sKVar≠
  SubstConVK𝑐 sHole = sKId
  SubstConVK𝑐 (sLet sub) = sKFun (λ x → SubstVK𝑐 (sub x))


  SubstVK𝑐 : {var : cpstyp → Set} {cvar : conttyp → Set} {τ τ₃ α β : typ𝑘} →
             {e₁ : var (cpsT𝑘 τ) → cvar (cpsT𝑘𝑐 (α ▷ β)) →
                   term𝑘[ var ∘ cpsT𝑘 , cvar ∘ cpsT𝑘𝑐 ] τ₃} →
             {e₂ : term𝑘[ var ∘ cpsT𝑘 , cvar ∘ cpsT𝑘𝑐 ] τ₃} →
             {v  : value𝑘[ var ∘ cpsT𝑘 , cvar ∘ cpsT𝑘𝑐 ] τ cps[τ,τ]} →
             {K𝑐 : pcontext𝑘[ var ∘ cpsT𝑘 , cvar ∘ cpsT𝑘𝑐 ] (α ▷ β)} →
             Subst𝑘 e₁ v K𝑐 e₂ →
             cpsSubst𝑐 {var} {cvar}
                       (λ y k → cpsE𝑘 (e₁ y k))
                       (cpsV𝑘 v) (cpsC𝑘 K𝑐)
                       (cpsE𝑘 e₂)
  SubstVK𝑐 (sVal sub-k sub-v)       = sRet (SubstConVK𝑐 sub-k) (SubstValV𝑐 sub-v)
  SubstVK𝑐 (sApp sub-k sub-v sub-w) = sApp (SubstValV𝑐 sub-v) (SubstValV𝑐 sub-w) (SubstConVK𝑐 sub-k)
  SubstVK𝑐 (sReset sub-k sub-e)     = sRetE (SubstConVK𝑐 sub-k) (SubstVK𝑐 sub-e)

