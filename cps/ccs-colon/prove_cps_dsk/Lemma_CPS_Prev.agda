module Lemma_CPS_Prev where

open import DStermK
open import CPSterm
open import CPSIsm
open import Lemma_CPS_Subst

open import Function
open import Relation.Binary.PropositionalEquality
                   
correctTerm𝑐 : {var : cpstyp → Set} {cvar : conttyp → Set} → {τ₁ : typ𝑘} →
               {e  : term𝑘[ var ∘ cpsT𝑘 , cvar ∘ cpsT𝑘𝑐 ] τ₁} →
               {e′ : term𝑘[ var ∘ cpsT𝑘 , cvar ∘ cpsT𝑘𝑐 ] τ₁} →
               ReduceTerm𝑘 e e′ →
               cpsReduce {var} {cvar}
                         (cpsE𝑘 e)
                         (cpsE𝑘 e′)
correctTerm𝑐 (βVal sub) = βVal𝑐 (SubstVK𝑐 sub)
correctTerm𝑐 (βLet sub) = βLet𝑐 (SubstV𝑐 sub)


correctTerm𝑐𝑠 : {var : cpstyp → Set} {cvar : conttyp → Set} → {τ₁ : typ𝑘} →
                {e  : term𝑘[ var ∘ cpsT𝑘 , cvar ∘ cpsT𝑘𝑐 ] τ₁} →
                {e′ : term𝑘[ var ∘ cpsT𝑘 , cvar ∘ cpsT𝑘𝑐 ] τ₁} →
                ReduceTerm𝑘𝑠 (RetE Hole e)
                             (RetE Hole e′) →
                cpsReduce• {var} {cvar}
                           (cpsE𝑘 e) (cpsE𝑘 e′)
correctTerm𝑐𝑠 βShift = βShift𝑐

correctTerm𝑐𝑅 : {var : cpstyp → Set} {cvar : conttyp → Set} → {τ₁ : typ𝑘} →
                {e : term𝑘[ var ∘ cpsT𝑘 , cvar ∘ cpsT𝑘𝑐 ] τ₁} →
                {v : value𝑘[ var ∘ cpsT𝑘 , cvar ∘ cpsT𝑘𝑐 ] τ₁ cps[τ,τ]} → 
                ReduceTerm𝑘𝑅 (RetE Hole e) v → 
                cpsReduce𝑅 {var} {cvar}
                           (cpsE𝑘 e) (cpsV𝑘 v)
correctTerm𝑐𝑅 βReset = βReset𝑐

correctVal𝑐 : {var : cpstyp → Set} {cvar : conttyp → Set} → {τ₁ : typ𝑘} →
              {v  : value𝑘[ var ∘ cpsT𝑘 , cvar ∘ cpsT𝑘𝑐 ] τ₁ cps[τ,τ]} → 
              {v′ : value𝑘[ var ∘ cpsT𝑘 , cvar ∘ cpsT𝑘𝑐 ] τ₁ cps[τ,τ]} →
              ReduceVal𝑘 v v′ →
              cpsReduceV {var} {cvar} (cpsV𝑘 v) (cpsV𝑘 v′)
correctVal𝑐 ηVal = ηVal𝑐

correctCon𝑐 : {var : cpstyp → Set} {cvar : conttyp → Set} → {τ₁ τ₂ : typ𝑘} →
              {p  : pcontext𝑘[ var ∘ cpsT𝑘 , cvar ∘ cpsT𝑘𝑐 ] (τ₁ ▷ τ₂)} →
              {p′ : pcontext𝑘[ var ∘ cpsT𝑘 , cvar ∘ cpsT𝑘𝑐 ] (τ₁ ▷ τ₂)} →
              ReduceCon𝑘 p p′ →
              cpsReduceK {var} {cvar} (cpsC𝑘 p) (cpsC𝑘 p′)
correctCon𝑐 ηLet = ηLet𝑐
