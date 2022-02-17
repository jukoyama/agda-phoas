module Lemma_DS_Prev where

open import CPSterm
open import DStermK
open import DSTrans
open import Lemma_DS_Subst

open import Function
open import Relation.Binary.PropositionalEquality

correctTerm𝑘 : {var : typ𝑘 → Set} {cvar : typ𝑘𝑐 → Set} → {τ₃ τ₅ : cpstyp} → 
               {e  : cpsterm𝑐[ var ∘ dsT , cvar ∘ dsT𝑐 ] τ₃} →
               {e′ : cpsterm𝑐[ var ∘ dsT , cvar ∘ dsT𝑐 ] τ₃} →
               cpsReduce e e′ → 
               ReduceTerm𝑘 {var} {cvar} (dsE𝑐 e) (dsE𝑐 e′)
               
correctTerm𝑘 (βVal𝑐 sub) = βVal (eSubstVK𝑘 sub)
correctTerm𝑘 (βLet𝑐 sub) = βLet (eSubstV𝑘 sub)
  
correctTermId𝑘 : {var : typ𝑘 → Set} {cvar : typ𝑘𝑐 → Set} → {τ₃ τ₅ : cpstyp} → 
                 {e  : cpsterm𝑐[ var ∘ dsT , cvar ∘ dsT𝑐 ] τ₃} →
                 {e′ : cpsterm𝑐[ var ∘ dsT , cvar ∘ dsT𝑐 ] τ₃} →
                 cpsReduce• e e′ → 
                 ReduceTerm𝑘𝑠 {var} {cvar}
                   (RetE Hole (dsE𝑐 e))
                   (RetE Hole (dsE𝑐 e′))
correctTermId𝑘 βShift𝑐 = βShift

correctTermId𝑘𝑆 : {var : typ𝑘 → Set} {cvar : typ𝑘𝑐 → Set} → {τ₂ : cpstyp} →
                  {e : cpsterm𝑐[ var ∘ dsT , cvar ∘ dsT𝑐 ] τ₂} →
                  {v : cpsvalue𝑐[ var ∘ dsT , cvar ∘ dsT𝑐 ] τ₂} →
                  cpsReduce𝑅 e v →
                  ReduceTerm𝑘𝑅 {var} {cvar}
                               (RetE Hole (dsE𝑐 e))
                               (dsV𝑐 v)
correctTermId𝑘𝑆 βReset𝑐 = βReset

correctVal𝑘 : {var : typ𝑘 → Set} {cvar : typ𝑘𝑐 → Set} → {τ₁ : cpstyp} →
              {v  : cpsvalue𝑐[ var ∘ dsT , cvar ∘ dsT𝑐 ] τ₁} →
              {v′ : cpsvalue𝑐[ var ∘ dsT , cvar ∘ dsT𝑐 ] τ₁} →
              cpsReduceV v v′ →
              ReduceVal𝑘 {var} {cvar} (dsV𝑐 v) (dsV𝑐 v′)
correctVal𝑘 ηVal𝑐 = ηVal

correctCon𝑘 : {var : typ𝑘 → Set} {cvar : typ𝑘𝑐 → Set} → {τ₁ τ₂ : cpstyp} →
              {k  : cpscont𝑐[ var ∘ dsT , cvar ∘ dsT𝑐 ] (τ₁ ⇒ τ₂)} →
              {k′ : cpscont𝑐[ var ∘ dsT , cvar ∘ dsT𝑐 ] (τ₁ ⇒ τ₂)} →
              cpsReduceK k k′ →
              ReduceCon𝑘 {var} {cvar} (dsC𝑐 k) (dsC𝑐 k′)
correctCon𝑘 ηLet𝑐 = ηLet
