module Lemma_CPS_Prev2 where

open import DStermK2
open import CPSterm2
open import CPSIsm2
open import Lemma_CPS_Subst2

open import Function
open import Relation.Binary.PropositionalEquality

correctRoot𝑐 : {var : cpstyp → Set} → {τ₁ τ₂ τ₃ : typ𝑘} →
               {e  : root𝑘[ var ∘ cpsT𝑘 ] τ₁ cps[ τ₂ , τ₃ ]} →
               {e′ : root𝑘[ var ∘ cpsT𝑘 ] τ₁ cps[ τ₂ , τ₃ ]} →
               ReduceRoot𝑘 e e′ →
               cpsReduceR {var} (λ k → cpsMain𝑘 τ₁ τ₂ τ₃ e k)
                                (λ k → cpsMain𝑘 τ₁ τ₂ τ₃ e′ k)
correctRoot𝑐 {var} {τ₁} {τ₂} {τ₃}
             {.(Root {_} {τ₁} {τ₂} {τ₃}
               (λ k → NonVal {_} {τ₄} {τ₂} {τ₃} {τ₂} K𝑐
                    (App {_} {τ₄} {τ₅} {τ₂} {τ₃} (Fun τ₄ τ₅ {τ₂} {τ₃}
                    (λ x → Root {_} {τ₄} {τ₂} {τ₃} (e x))) v)))}
             {.(Root {_} {τ₁} {τ₂} {τ₃} (λ k → e′))}
             (βVal {τ = .τ₁} {τ₁ = τ₄} {τ₂ = τ₅} {τ₃ = .τ₂} {τ₄ = .τ₃}
                      {K𝑐 = K𝑐} {e = e} {v = v} {e′ = e′} sub) =
  βVal𝑐 (SubstVK𝑐 sub)               
                   
correctTerm𝑐 : {var : cpstyp → Set} → {τ₁ τ₂ τ₃ : typ𝑘} →
               {e  : term𝑘[ var ∘ cpsT𝑘 ] τ₂ cps[ τ₂ , τ₃ ]} →
               {e′ : term𝑘[ var ∘ cpsT𝑘 ] τ₂ cps[ τ₂ , τ₃ ]} →
               ReduceTerm𝑘 e e′ →
               cpsReduce {var} (cpsE𝑘 τ₃ τ₂ e)
                               (cpsE𝑘 τ₃ τ₂ e′)
correctTerm𝑐 {var} {τ₁} {τ₂} {τ₃}
             {.(Val {_} {τ₄} {τ₃} {τ₂} (KLet {_} {τ₄} {τ₂} {τ₃} {τ₃} e₂) v)} {e′}
             (βLet {τ₁ = τ₄} {τ₂ = .τ₂} {β = .τ₃} {e₂ = e₂} {v = v} {e₂′ = .e′} sub) =
  βLet𝑐 (SubstV𝑐 sub)

correctTerm𝑐𝑠 : {var : cpstyp → Set} → {τ₁ τ₂ τ₃ : typ𝑘} →
                {e  : term𝑘[ var ∘ cpsT𝑘 ] τ₂ cps[ τ₂ , τ₃ ]} →
                {e′ : term𝑘[ var ∘ cpsT𝑘 ] τ₂ cps[ τ₂ , τ₃ ]} →
                ReduceTerm𝑘𝑠 (NonVal Hole (Reset τ₂ τ₃ τ₃ e))
                             (NonVal Hole (Reset τ₂ τ₃ τ₃ e′)) →
                cpsReduce• {var} (cpsE𝑘 τ₃ τ₂ e)
                                 (cpsE𝑘 τ₃ τ₂ e′)
correctTerm𝑐𝑠 {var} {τ₁} {τ₂} {τ₃}
              {.(NonVal {_} {τ₅} {τ₃} {τ₃} {τ₂} K𝑐
                (App {_} {τ₅} {(τ₅ ⇒ τ₃ cps[ τ , τ ]) ⇒ τ₂ cps[ τ₂ , τ₃ ]} {τ₃} {τ₃}
                     (Shift {_} {τ} {τ₂} {τ₃} {τ₅} {τ₃}) w))}
              {.(NonVal {_} {τ₂} {τ₂} {τ₃} {τ₂} (Hole {_} {τ₂} {τ₃})
                (App {_} {τ₂} {τ₅ ⇒ τ₃ cps[ τ , τ ]} {τ₂} {τ₃}
                     w
                     (Fun τ₃ τ₅ {τ} {τ} (λ y → Root {_} {τ₃} {τ} {τ}
                          (λ k → NonVal {_} {τ₃} {τ} {τ} {τ} (KHole {_} {τ₃} {τ} {τ} k)
                                 (Reset τ₂ τ₃ τ (Val {_} {τ₅} {τ₃} {τ₂} K𝑐 (Var {_} {τ₅} y))))))))}
              (βShift {τ = τ} {τ₁ = .τ₂} {τ₂ = τ₄} {τ₃ = τ₅} {τ₄ = .τ₃} {τ₅ = .τ₂}
                      {K𝑐 = K𝑐} {w = w}) =
  βShift𝑐
  
correctVal𝑐 : {var : cpstyp → Set} → {τ₁ : typ𝑘} →
              {v  : value𝑘[ var ∘ cpsT𝑘 ] τ₁ cps[τ,τ]} → 
              {v′ : value𝑘[ var ∘ cpsT𝑘 ] τ₁ cps[τ,τ]} →
              ReduceVal𝑘 v v′ →
              cpsReduceV {var} (cpsV𝑘 τ₁ v) (cpsV𝑘 τ₁ v′)
correctVal𝑐 {var} {.(τ₂ ⇒ τ₁ cps[ τ₃ , τ₄ ])}
            {.(Fun τ₁ τ₂ {τ₃} {τ₄} (λ x → Root {_} {τ₁} {τ₃} {τ₄} (λ k →
              NonVal {_} {τ₁} {τ₃} {τ₄} {τ₃}
                     (KHole {_} {τ₁} {τ₃} {τ₄} k)
                     (App {_} {τ₁} {τ₂} {τ₃} {τ₄} v′ (Var {_} {τ₂} x)))))}
            {v′}
            (ηVal {τ₁ = τ₁} {τ₂ = τ₂} {τ₃ = τ₃} {τ₄ = τ₄} {v = .v′}) =
  ηVal𝑐

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
