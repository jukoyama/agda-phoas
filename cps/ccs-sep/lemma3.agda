module lemma3 where

open import DSterm
open import CPSterm
open import lemma1
open import lemma2

open import Function
open import Relation.Binary.PropositionalEquality

subst-context : {var : typ → Set} {τ₂ τ₃ τ₄ τ₀ : typ} →
                (con : pcontext[ var , τ₀ cps[ τ₂ , τ₂ ]] τ₄ cps[ τ₃ , τ₂ ]) →
                (v : value[ var ] τ₀ cps[τ,τ]) →
                Subst (λ x → pcontext-plug con (Val (Var x)))
                      v
                      (pcontext-plug con (Val v))
subst-context {var} {τ₂} {.τ₂} {τ₄} {.τ₄} (Hole {τ₁ = .τ₄} {τ₂ = .τ₂} {τ₃ = .τ₂}) v = sVal sVar=

subst-context {var} {τ₂} {τ₃} {τ₄} {τ₀}
              (Frame {τ₁ = .τ₀} {τ₂ = .τ₂} {τ₃ = .τ₂} {τ₄ = .(τ₅ ⇒ τ₄ cps[ τ₃ , τ₇ ])}
                     {τ₅ = τ₆} {τ₆ = .τ₂} {τ₇ = .τ₄} {τ₈ = .τ₃} {τ₉ = .τ₂}
              (App₁ {τ₁ = .τ₄} {τ₂ = τ₅} {τ₃ = .τ₃} {τ₄ = τ₇} {τ₅ = .τ₆} {τ₆ = .τ₂} e₂) con′)
              v = sApp (subst-context con′ v) DSubst≠

subst-context {var} {τ₂} {τ₃} {τ₄} {τ₀}
              (Frame {τ₁ = .τ₀} {τ₂ = .τ₂} {τ₃ = .τ₂} {τ₄ = τ₅} {τ₅ = τ₆} {τ₆ = .τ₂}
                     {τ₇ = .τ₄} {τ₈ = .τ₃} {τ₉ = .τ₂}
              (App₂ {τ₁ = .τ₄} {τ₂ = .τ₅} {τ₃ = .τ₃} {τ₄ = .τ₆} {τ₅ = .τ₂} v₁) con′)
              v = sApp DSubst≠ (subst-context con′ v)

subst-context {var} {τ₂} {τ₃} {τ₄} {τ₀}
              (Frame {τ₁ = .τ₀} {τ₂ = .τ₂} {τ₃ = .τ₂} {τ₄ = τ₅} {τ₅ = τ₆} {τ₆ = .τ₂}
                     {τ₇ = .τ₄} {τ₈ = .τ₃} {τ₉ = .τ₂}
              (Let {τ₁ = .τ₅} {τ₂ = .τ₄} {α = .τ₃} {β = .τ₆} {γ = .τ₂} e₂) con′)
              v = sLet (λ x → DSubst≠) (subst-context con′ v)
              
