module Lemma_CPS_Prev where

open import DStermK
open import CPSterm
open import CPSIsm
open import Lemma_CPS_Subst

open import Function
open import Relation.Binary.PropositionalEquality
                   
correctTerm𝑐 : {var : cpstyp → Set} → {τ₁ τ₂ τ₃ : typ𝑘} →
               {e  : term𝑘[ var ∘ cpsT𝑘 ] τ₂ cps[ τ₂ , τ₃ ]} →
               {e′ : term𝑘[ var ∘ cpsT𝑘 ] τ₂ cps[ τ₂ , τ₃ ]} →
               ReduceTerm𝑘 e e′ →
               cpsReduce {var} (cpsE𝑘 τ₃ τ₂ e)
                               (cpsE𝑘 τ₃ τ₂ e′)
correctTerm𝑐 {var} {τ₁} {τ₂} {τ₃} {.(NonVal {_} {τ₄} {τ₅} {τ₃} {τ₂} K𝑐 (App {_} {τ₄} {τ₀} {τ₅} {τ₃} (Fun τ₀ τ₂ τ₄ τ₂ {τ₅} {τ₃} e) v))} {e′} (βVal {τ = τ} {τ₀ = τ₀} {τ₁ = τ₄} {τ₂ = .τ₂} {τ₃ = τ₅} {τ₄ = .τ₃} {K𝑐 = K𝑐} {e = e} {v = v} {e′ = .e′} sub) = βVal𝑐 (SubstVK𝑐 sub)
correctTerm𝑐 {var} {τ₁} {τ₂} {τ₃} {.(Val {_} {τ₄} {τ₃} {τ₂} (KLet {_} {τ₄} {τ₂} {τ₃} {τ₃} e₂) v)} {e′} (βLet {τ₁ = τ₄} {τ₂ = .τ₂} {β = .τ₃} {e₂ = e₂} {v = v} {e₂′ = .e′} sub) = βLet𝑐 (SubstV𝑐 sub)

correctTerm𝑐𝑠 : {var : cpstyp → Set} → {τ₁ τ₂ τ₃ : typ𝑘} →
                {e  : term𝑘[ var ∘ cpsT𝑘 ] τ₂ cps[ τ₂ , τ₃ ]} →
                {e′ : term𝑘[ var ∘ cpsT𝑘 ] τ₂ cps[ τ₂ , τ₃ ]} →
                ReduceTerm𝑘𝑠 (NonVal Hole (Reset τ₂ τ₃ τ₃ e))
                             (NonVal Hole (Reset τ₂ τ₃ τ₃ e′)) →
                cpsReduce• {var} (cpsE𝑘 τ₃ τ₂ e)
                                 (cpsE𝑘 τ₃ τ₂ e′)
correctTerm𝑐𝑠 {var} {τ₁} {τ₂} {τ₃}
              {.(NonVal {_} {τ₄} {τ₃} {τ₃} {τ₂}
                        J
                        (App {_} {τ₄} {(τ₄ ⇒ τ₃ cps[ τ₄ , τ₄ ]) ⇒ τ₂ cps[ τ₂ , τ₃ ]} {τ₃} {τ₃}
                             (Shift {_} {τ₄} {τ₂} {τ₃} {τ₄} {τ₃})
                             w))}
              {.(NonVal {_} {τ₂} {τ₂} {τ₃} {τ₂}
                        (Hole {_} {τ₂} {τ₃})
                        (App {_} {τ₂} {τ₄ ⇒ τ₃ cps[ τ₄ , τ₄ ]} {τ₂} {τ₃}
                             w
                             (Fun τ₄ τ₄ τ₃ τ₄ {τ₄} {τ₄} (λ y k →
                                  NonVal {_} {τ₃} {τ₄} {τ₄} {τ₄}
                                         (KHole {_} {τ₃} {τ₄} {τ₄} k)
                                         (Reset τ₂ τ₃ τ₄
                                                (Val {_} {τ₄} {τ₃} {τ₂}
                                                     J (Var {_} {τ₄} y)))))))}
              (βShift {τ₁ = .τ₂} {τ₃ = τ₄} {τ₄ = .τ₃} {J = J} {w = w}) =
  βShift𝑐

correctTerm𝑐𝑅 : {var : cpstyp → Set} → {τ₂ : typ𝑘} →
                {e : term𝑘[ var ∘ cpsT𝑘 ] τ₂ cps[ τ₂ , τ₂ ]} →
                {v : value𝑘[ var ∘ cpsT𝑘 ] τ₂ cps[τ,τ]} → 
                ReduceTerm𝑘𝑅 (NonVal Hole (Reset τ₂ τ₂ τ₂ e))
                             v → 
                cpsReduce𝑅 {var} (cpsE𝑘 τ₂ τ₂ e)
                                 (cpsV𝑘 τ₂ v)
correctTerm𝑐𝑅 {var} {τ₂}
              {.(Val {_} {τ₂} {τ₂} {τ₂}
              (Hole {_} {τ₂} {τ₂}) v)} {v}
              (βReset {τ₁ = .τ₂} {v = .v}) =
  βReset𝑐
  
correctVal𝑐 : {var : cpstyp → Set} → {τ₁ : typ𝑘} →
              {v  : value𝑘[ var ∘ cpsT𝑘 ] τ₁ cps[τ,τ]} → 
              {v′ : value𝑘[ var ∘ cpsT𝑘 ] τ₁ cps[τ,τ]} →
              ReduceVal𝑘 v v′ →
              cpsReduceV {var} (cpsV𝑘 τ₁ v) (cpsV𝑘 τ₁ v′)
correctVal𝑐 = {!!}
-- correctVal𝑐 {var} {.(τ₂ ⇒ τ₁ cps[ τ₃ , τ₄ ])}
--             {.(Fun τ₁ τ₂ {τ₃} {τ₄} (λ x → Root {_} {τ₁} {τ₃} {τ₄} (λ k →
--               NonVal {_} {τ₁} {τ₃} {τ₄} {τ₃}
--                      (KHole {_} {τ₁} {τ₃} {τ₄} k)
--                      (App {_} {τ₁} {τ₂} {τ₃} {τ₄} v′ (Var {_} {τ₂} x)))))}
--             {v′}
--             (ηVal {τ₁ = τ₁} {τ₂ = τ₂} {τ₃ = τ₃} {τ₄ = τ₄} {v = .v′}) =
--   ηVal𝑐

correctCon𝑐 : {var : cpstyp → Set} → {τ₁ τ₂ τ₃ τ₇ τ₈ : typ𝑘} →
              {p  : pcontext𝑘[ var ∘ cpsT𝑘 , τ₁ cps[ τ₂ , τ₃ ]] τ₇
                            cps[ τ₇ , τ₃ ]} →
              {p′ : pcontext𝑘[ var ∘ cpsT𝑘 , τ₁ cps[ τ₂ , τ₃ ]] τ₇
                            cps[ τ₇ , τ₃ ]} →
              ReduceCon𝑘 p p′ →
              cpsReduceK {var} (cpsC𝑘 τ₁ τ₂ τ₃ τ₇ p)
                               (cpsC𝑘 τ₁ τ₂ τ₃ τ₇ p′)
correctCon𝑐 {var} {τ₁} {τ₂} {.τ₂} {τ₇} {τ₈}
            {.(KLet {_} {τ₁} {τ₇} {τ₂} {τ₂}
              (λ x → Val {_} {τ₁} {τ₂} {τ₇} p′ (Var {_} {τ₁} x)))} {p′}
            (ηLet {τ₁ = .τ₁} {τ₂ = .τ₇} {β = .τ₂} {K𝑐 = .p′}) =
  ηLet𝑐
