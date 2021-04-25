module CPSProve where

open import DSterm
open import CPSterm
open import reasoning

open import Function
open import Relation.Binary.PropositionalEquality

{----------------Term Definition----------------}

correctEta : {var : cpstyp → Set} → {τ₁ τ₂ τ₃ : typ} →
             {e  : term[ var ∘ cpsT ] τ₁ cps[ τ₂ , τ₃ ]} →
             {e′ : term[ var ∘ cpsT ] τ₁ cps[ τ₂ , τ₃ ]} →
             {κ : cpscont𝑐[ var ] (cpsT τ₁ ⇒ cpsT τ₂)} →
             Reduce e e′ →
             cpsReduce (cpsE𝑐 τ₁ τ₂ τ₃ e κ) (cpsE𝑐 τ₁ τ₂ τ₃ e′ κ)
             
correctEta {var} {τ₁} {τ₂} {τ₃}
           {.(NonVal {_} {τ₁} {τ₂} {τ₃}
                     (App {_} {τ₁} {τ} {τ₂} {τ₃} {τ₃} {τ₃}
                          (Val {_} {τ ⇒ τ₁ cps[ τ₂ , τ₃ ]} {τ₃} (Fun τ₁ τ {τ₂} {τ₃} e₁))
                          (Val {_} {τ} {τ₃} v₂)))}
           {e′} {κ}
           (RBeta {τ = τ} {τ₁ = .τ₁} {τ₂ = .τ₂} {τ₃ = .τ₃} {e₁ = e₁} {v₂ = v₂} {e₁′ = .e′} sub) = {!!}

correctEta {var} {τ₁} {τ₂} {τ₃} {.(frame-plug {λ x → var (cpsT x)} {τ₁} {τ₄} {τ₂} {τ₅} {τ₆} {τ₃} f e₁)} {.(frame-plug {λ x → var (cpsT x)} {τ₁} {τ₄} {τ₂} {τ₅} {τ₆} {τ₃} f e₂)} {κ} (RFrame {τ₁ = τ₄} {τ₂ = τ₅} {τ₃ = τ₆} {τ₄ = .τ₁} {τ₅ = .τ₂} {τ₆ = .τ₃} {e₁ = e₁} {e₂ = e₂} f e) = {!!}

correctEta {var} {τ₁} {τ₂} {τ₃} {.(NonVal {_} {τ₁} {τ₂} {τ₃} (Let {_} {τ₄} {τ₁} {τ₂} {τ₃} {τ₃} (Val {_} {τ₄} {τ₃} v₁) e₂))} {e′} {κ} (RLet {τ₁ = τ₄} {τ₂ = .τ₁} {α = .τ₂} {β = .τ₃} {v₁ = v₁} {e₂ = e₂} {e₂′ = .e′} x) = {!!}

correctEta {var} {τ₁} {τ₂} {.τ₂} {.(NonVal {_} {τ₁} {τ₂} {τ₂} (Reset τ₁ τ₁ τ₂ (Val {_} {τ₁} {τ₁} v₁)))} {.(Val {_} {τ₁} {τ₂} v₁)} {κ} (RReset {τ₁ = .τ₁} {τ₂ = .τ₂} {v₁ = v₁}) = {!!}

correctEta {var} {τ₁} {τ₂} {.τ₂} {.(NonVal {_} {τ₁} {τ₂} {τ₂} (Reset τ₆ τ₁ τ₂ (pcontext-plug {λ x₁ → var (cpsT x₁)} {τ₄} {τ₅} {τ₁} {τ₆} {τ₆} {τ₁} p₁ (NonVal {_} {τ₄} {τ₅} {τ₁} (App {_} {τ₄} {(τ₄ ⇒ τ₅ cps[ τ , τ ]) ⇒ τ₃ cps[ τ₃ , τ₁ ]} {τ₅} {τ₁} {τ₁} {τ₁} (Val {_} {((τ₄ ⇒ τ₅ cps[ τ , τ ]) ⇒ τ₃ cps[ τ₃ , τ₁ ]) ⇒ τ₄ cps[ τ₅ , τ₁ ]} {τ₁} (Shift {_} {τ} {τ₃} {τ₁} {τ₄} {τ₅})) (Val {_} {(τ₄ ⇒ τ₅ cps[ τ , τ ]) ⇒ τ₃ cps[ τ₃ , τ₁ ]} {τ₁} v₂))))))} {.(NonVal {_} {τ₁} {τ₂} {τ₂} (Reset τ₃ τ₁ τ₂ (NonVal {_} {τ₃} {τ₃} {τ₁} (App {_} {τ₃} {τ₄ ⇒ τ₅ cps[ τ , τ ]} {τ₃} {τ₁} {τ₁} {τ₁} (Val {_} {(τ₄ ⇒ τ₅ cps[ τ , τ ]) ⇒ τ₃ cps[ τ₃ , τ₁ ]} {τ₁} v₂) (Val {_} {τ₄ ⇒ τ₅ cps[ τ , τ ]} {τ₁} (Fun τ₅ τ₄ {τ} {τ} (λ x₁ → NonVal {_} {τ₅} {τ} {τ} (Reset τ₆ τ₅ τ (pcontext-plug {λ x₂ → var (cpsT x₂)} {τ₄} {τ₅} {τ₅} {τ₆} {τ₆} {τ₅} p₂ (Val {_} {τ₄} {τ₅} (Var {_} {τ₄} x₁)))))))))))} {κ} (RShift {τ = τ} {τ₁ = τ₃} {τ₂ = .τ₁} {τ₃ = τ₄} {τ₄ = τ₅} {τ₅ = τ₆} {τ₆ = .τ₂} {v₂ = v₂} p₁ p₂ x) = {!!}
