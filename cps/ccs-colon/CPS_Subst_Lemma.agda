module CPS_Subst_Lemma where

open import CPSterm
open import DStermK
open import CPSIsm

open import Function

mutual
  cpsSubstV𝑐≠ : {var : cpstyp → Set} {τ₁ τ₂ : cpstyp} →
                {t : cpsvalue𝑐[ var ] τ₁} →
                {v : cpsvalue𝑐[ var ] τ₂} →
                cpsSubstValV𝑐 (λ y → t) v t
  cpsSubstV𝑐≠ = {!!}

  Subst≠ : {var : cpstyp → Set} {τ₁ τ₂ τ₃ : cpstyp} →
           {t : cpsterm𝑐[ var ] (τ₃ ⇒ τ₃) τ₁} →
           {v : cpsvalue𝑐[ var ] τ₂} →
           {!!}
  Subst≠ = {!!}

mutual
  SubstValV𝑐 : {var : cpstyp → Set} {τ₁ τ : typ𝑘} →
               {v₁ : var (cpsT𝑘 τ) → value𝑘[ var ∘ cpsT𝑘 ] τ₁ cps[τ,τ]} →
               {v₂ : value𝑘[ var ∘ cpsT𝑘 ] τ₁ cps[τ,τ]} →
               {v  : value𝑘[ var ∘ cpsT𝑘 ] τ cps[τ,τ]} →
               SubstValV𝑘 v₁ v v₂ →
               cpsSubstValV𝑐 {var} (λ y → cpsV𝑘 τ₁ (v₁ y))
                                   (cpsV𝑘 τ v)
                                   (cpsV𝑘 τ₁ v₂)
  SubstValV𝑐 = {!!}

  SubstConVK𝑐 : {var : cpstyp → Set} {τ τ₁ τ₂ τ₃ τ₄ α β γ ε ζ : typ𝑘} →
                {k₁ : var (cpsT𝑘 τ) →
                      pcontext𝑘[ var ∘ cpsT𝑘 , τ₁ cps[ τ₂ , τ₃ ]] τ₄
                              cps[ τ₄ , τ₃ ]} →
                {k₂ : pcontext𝑘[ var ∘ cpsT𝑘  , τ₁ cps[ τ₂ , τ₃ ]] τ₄
                             cps[ τ₄ , τ₃ ]} →
                {v  : value𝑘[ var ∘ cpsT𝑘 ] τ cps[τ,τ]} →
                {K𝑐 : pcontext𝑘[ var ∘ cpsT𝑘 , α cps[ β , γ ]] ε cps[ ζ , γ ]} → 
                SubstCon𝑘 {!k₁!} v K𝑐 {!!} →
                cpsSubstCont𝑐 {!!}
                              (cpsV𝑘 {!!} v)
                              (cpsC𝑘 {!!} {!!} {!!} {!!} {!K𝑐!})
                              {!!}
  SubstConVK𝑐 = {!!}


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
  SubstConV𝑐 = {!!}

  SubstV𝑐 : {var : cpstyp → Set} {τ τ₂ τ₃ : typ𝑘} →
            {e₁ : var (cpsT𝑘 τ) →
                  term𝑘[ var ∘ cpsT𝑘 ] τ₂ cps[ τ₂ , τ₃ ]} →
            {e₂ : term𝑘[ var ∘ cpsT𝑘 ] τ₂ cps[ τ₂ , τ₃ ]} →
            {v  : value𝑘[ var ∘ cpsT𝑘 ] τ cps[τ,τ]} →
            SubstV𝑘 e₁ v e₂ →
            cpsSubstV𝑐 {var} (λ y → cpsE𝑘 τ₃ τ₂ (e₁ y))
                             (cpsV𝑘 τ v)
                             (cpsE𝑘 τ₃ τ₂ e₂)
  SubstV𝑐 = {!!}

