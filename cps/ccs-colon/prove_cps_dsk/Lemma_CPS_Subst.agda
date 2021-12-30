module Lemma_CPS_Subst where

open import CPSterm
open import DStermK
open import CPSIsm

open import Function
open import Relation.Binary.PropositionalEquality

mutual
  SubstValV𝑐 : {var : cpstyp → Set} {τ₁ τ : typ𝑘} →
               {v₁ : var (cpsT𝑘 τ) → value𝑘[ var ∘ cpsT𝑘 ] τ₁ cps[τ,τ]} →
               {v₂ : value𝑘[ var ∘ cpsT𝑘 ] τ₁ cps[τ,τ]} →
               {v  : value𝑘[ var ∘ cpsT𝑘 ] τ cps[τ,τ]} →
               SubstValV𝑘 v₁ v v₂ →
               cpsSubstValV𝑐 {var} (λ y → cpsV𝑘 τ₁ (v₁ y))
                                   (cpsV𝑘 τ v)
                                   (cpsV𝑘 τ₁ v₂)
  SubstValV𝑐 SubstValV𝑘.sVar= = cpsSubstValV𝑐.sVar=
  SubstValV𝑐 SubstValV𝑘.sVar≠ = cpsSubstValV𝑐.sVar≠
  SubstValV𝑐 SubstValV𝑘.sNum  = cpsSubstValV𝑐.sNum
  SubstValV𝑐 SubstValV𝑘.sShift = cpsSubstValV𝑐.sShift
  SubstValV𝑐 (SubstValV𝑘.sFun sub) =
    sFun (λ x k → SubstRootV𝑐 k (sub x))

  SubstConV𝑐 : {var : cpstyp → Set} {τ τ₁ τ₂ τ₃ τ₄ : typ𝑘} →
               {k₁ : var (cpsT𝑘 τ) → pcontext𝑘[ var ∘ cpsT𝑘 , τ₁ cps[ τ₂ , τ₃ ]] τ₄
                                    cps[ τ₄ , τ₃ ]} →
               {k₂ : pcontext𝑘[ var ∘ cpsT𝑘  , τ₁ cps[ τ₂ , τ₃ ]] τ₄
                             cps[ τ₄ , τ₃ ]} →
               {v  : value𝑘[ var ∘ cpsT𝑘 ] τ cps[τ,τ]} →
               SubstConV𝑘 k₁ v k₂ →
               cpsSubstContV𝑐 {var} (λ y → cpsC𝑘 τ₁ τ₂ τ₃ τ₄ (k₁ y))
                                    (cpsV𝑘 τ v)
                                    (cpsC𝑘 τ₁ τ₂ τ₃ τ₄ k₂)
  SubstConV𝑐 sConVar≠    = sKVar≠
  SubstConV𝑐 sConId      = sKId
  SubstConV𝑐 (sConLet sub-e) = sKFun (λ x → SubstV𝑐 (sub-e x))

  SubstRootV𝑐 : {var : cpstyp → Set} {τ τ₁ τ₂ τ₃ : typ𝑘} →
                (k  : var (cpsT𝑘 τ₁ ⇒[ cpsT𝑘 τ₂ ⇒ cpsT𝑘 τ₂ ]⇒ cpsT𝑘 τ₂)) → 
                {e₁ : var (cpsT𝑘 τ) →
                      root𝑘[ var ∘ cpsT𝑘 ] τ₁ cps[ τ₂ , τ₃ ]} →
                {e₂ : root𝑘[ var ∘ cpsT𝑘 ] τ₁ cps[ τ₂ , τ₃ ]} →
                {v  : value𝑘[ var ∘ cpsT𝑘 ] τ cps[τ,τ]} →
                SubstRootV𝑘 e₁ v e₂ →
                cpsSubstV𝑐 {var} (λ y → cpsMain𝑘 τ₁ τ₂ τ₃ (e₁ y) k)
                                 (cpsV𝑘 τ v)
                                 (cpsMain𝑘 τ₁ τ₂ τ₃ e₂ k)
  SubstRootV𝑐 k (sRoot sub) = SubstV𝑐 (sub k)

  SubstV𝑐 : {var : cpstyp → Set} {τ τ₂ τ₃ : typ𝑘} →
            {e₁ : var (cpsT𝑘 τ) →
                  term𝑘[ var ∘ cpsT𝑘 ] τ₂ cps[ τ₂ , τ₃ ]} →
            {e₂ : term𝑘[ var ∘ cpsT𝑘 ] τ₂ cps[ τ₂ , τ₃ ]} →
            {v  : value𝑘[ var ∘ cpsT𝑘 ] τ cps[τ,τ]} →
            SubstV𝑘 e₁ v e₂ →
            cpsSubstV𝑐 {var} (λ y → cpsE𝑘 τ₃ τ₂ (e₁ y))
                             (cpsV𝑘 τ v)
                             (cpsE𝑘 τ₃ τ₂ e₂)
  SubstV𝑐 (sVal sub-k sub-v)       = sRet (SubstConV𝑐 sub-k) (SubstValV𝑐 sub-v)
  SubstV𝑐 (sApp sub-k sub-v sub-w) = sApp (SubstValV𝑐 sub-v) (SubstValV𝑐 sub-w) (SubstConV𝑐 sub-k)
  SubstV𝑐 (sReset sub-k sub-e)     = sRetE (SubstConV𝑐 sub-k) (SubstV𝑐 sub-e)

mutual
  SubstConVK𝑐 : {var : cpstyp → Set} {τ τ₁ τ₂ τ₃ τ₄ α β γ ζ : typ𝑘} →
                {k₁ : var (cpsT𝑘 τ) → var (cpsT𝑘 (α ⇒ β cps[ ζ , ζ ])) → 
                      pcontext𝑘[ var ∘ cpsT𝑘 , τ₁ cps[ τ₂ , τ₃ ]] τ₄
                              cps[ τ₄ , τ₃ ]} →
                {k₂ : pcontext𝑘[ var ∘ cpsT𝑘  , τ₁ cps[ τ₂ , τ₃ ]] τ₄
                             cps[ τ₄ , τ₃ ]} →
                {v  : value𝑘[ var ∘ cpsT𝑘 ] τ cps[τ,τ]} →
                {K𝑐 : pcontext𝑘[ var ∘ cpsT𝑘 , α cps[ β , γ ]] ζ cps[ ζ , γ ]} → 
                SubstCon𝑘 k₁ v K𝑐 k₂ →
                cpsSubstCont𝑐 {var} (λ y k′ → cpsC𝑘 τ₁ τ₂ τ₃ τ₄ (k₁ y k′))
                                    (cpsV𝑘 τ v)
                                    (cpsC𝑘 α β γ ζ K𝑐)
                                    (cpsC𝑘 τ₁ τ₂ τ₃ τ₄ k₂)
  SubstConVK𝑐 sCon= = sKVar=
  SubstConVK𝑐 sCon≠ = sKVar≠
  SubstConVK𝑐 sHole = sKId
  SubstConVK𝑐 (sLet sub) = sKFun (λ x → SubstVK𝑐 (sub x))


  SubstVK𝑐 : {var : cpstyp → Set} {τ τ₂ τ₃ α β γ ζ : typ𝑘} →
             {e₁ : var (cpsT𝑘 τ) → var (cpsT𝑘 (α ⇒ β cps[ ζ , ζ ])) →
                   term𝑘[ var ∘ cpsT𝑘 ] τ₂ cps[ τ₂ , τ₃ ]} →
             {e₂ : term𝑘[ var ∘ cpsT𝑘 ] τ₂ cps[ τ₂ , τ₃ ]} →
             {v  : value𝑘[ var ∘ cpsT𝑘 ] τ cps[τ,τ]} →
             {K𝑐 : pcontext𝑘[ var ∘ cpsT𝑘 , α cps[ β , γ ]] ζ cps[ ζ , γ ]} →
             Subst𝑘 e₁ v K𝑐 e₂ →
             cpsSubst𝑐 {var} (λ y k → cpsE𝑘 τ₃ τ₂ (e₁ y k))
                             (cpsV𝑘 τ v) (cpsC𝑘 α β γ ζ K𝑐)
                             (cpsE𝑘 τ₃ τ₂ e₂)
  SubstVK𝑐 (sVal sub-k sub-v)       = sRet (SubstConVK𝑐 sub-k) (SubstValV𝑐 sub-v)
  SubstVK𝑐 (sApp sub-k sub-v sub-w) = sApp (SubstValV𝑐 sub-v) (SubstValV𝑐 sub-w) (SubstConVK𝑐 sub-k)
  SubstVK𝑐 (sReset sub-k sub-e)     = sRetE (SubstConVK𝑐 sub-k) (SubstVK𝑐 sub-e)

