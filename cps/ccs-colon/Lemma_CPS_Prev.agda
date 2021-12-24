module Lemma_CPS_Prev where

open import DStermK
open import CPSterm
open import CPSIsm

open import Function

correctRoot𝑐 : {var : cpstyp → Set} → {τ₁ τ₂ τ₃ : typ𝑘} →
               {e  : root𝑘[ var ∘ cpsT𝑘 ] τ₁ cps[ τ₂ , τ₃ ]} →
               {e′ : root𝑘[ var ∘ cpsT𝑘 ] τ₁ cps[ τ₂ , τ₃ ]} →
               ReduceRoot𝑘 e e′ →
               cpsReduce {var} (cpsMain𝑘 τ₁ τ₂ τ₃ e {!!})
                               (cpsMain𝑘 τ₁ τ₂ τ₃ e {!!})
correctRoot𝑐 = {!!}
               
                   
correctTerm𝑐 : {var : cpstyp → Set} → {τ₁ τ₂ τ₃ : typ𝑘} →
               {e  : term𝑘[ var ∘ cpsT𝑘 ] τ₂ cps[ τ₂ , τ₃ ]} →
               {e′ : term𝑘[ var ∘ cpsT𝑘 ] τ₂ cps[ τ₂ , τ₃ ]} →
               ReduceTerm𝑘 e e′ →
               cpsReduce {var} (cpsE𝑘 τ₃ τ₂ e)
                               (cpsE𝑘 τ₃ τ₂ e′)
correctTerm𝑐 = {!!}

correctVal𝑐 : {var : cpstyp → Set} → {τ₁ : typ𝑘} →
              {v  : value𝑘[ var ∘ cpsT𝑘 ] τ₁ cps[τ,τ]} → 
              {v′ : value𝑘[ var ∘ cpsT𝑘 ] τ₁ cps[τ,τ]} →
              ReduceVal𝑘 v v′ →
              cpsReduceV {var} (cpsV𝑘 τ₁ v) (cpsV𝑘 τ₁ v′)
correctVal𝑐 = {!!}

correctCon𝑐 : {var : cpstyp → Set} → {τ₁ τ₂ τ₃ τ₇ τ₈ : typ𝑘} →
              {p  : pcontext𝑘[ var ∘ cpsT𝑘 , τ₁ cps[ τ₂ , τ₃ ]] τ₇
                            cps[ τ₇ , τ₃ ]} →
              {p′ : pcontext𝑘[ var ∘ cpsT𝑘 , τ₁ cps[ τ₂ , τ₃ ]] τ₇
                            cps[ τ₇ , τ₃ ]} →
              ReduceCon𝑘 p p′ →
              cpsReduceK {var} (cpsC𝑘 τ₁ τ₂ τ₃ τ₇ p)
                               (cpsC𝑘 τ₁ τ₂ τ₃ τ₇ p′)
correctCon𝑐 = {!!}
