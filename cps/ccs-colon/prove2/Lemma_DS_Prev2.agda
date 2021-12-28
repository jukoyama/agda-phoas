module Lemma_DS_Prev2 where

open import CPSterm2
open import DStermK2
open import DSTrans2
open import reasoning2

open import Function
open import Relation.Binary.PropositionalEquality

correctRoot𝑘 : {var : typ𝑘 → Set} → {τ₁ τ₂ τ₃ : cpstyp} →
               {r  : (var ∘ dsT) (τ₁ ⇒[ τ₂ ⇒ τ₂ ]⇒ τ₂) →
                    cpsterm𝑐[ var ∘ dsT ] (τ₂ ⇒ τ₂) τ₃} →
               {r′ : (var ∘ dsT) (τ₁ ⇒[ τ₂ ⇒ τ₂ ]⇒ τ₂) →
                    cpsterm𝑐[ var ∘ dsT ] (τ₂ ⇒ τ₂) τ₃} →
               cpsReduceR r r′ → 
               ReduceRoot𝑘 {var} (dsMain𝑐 τ₁ τ₂ τ₃ r)
                                 (dsMain𝑐 τ₁ τ₂ τ₃ r′)
correctRoot𝑘 {var} {τ₁} {τ₂} {τ₃}
             {.(λ k → CPSApp {_} {τ′} {τ} {τ₂} {τ₃} {τ₂} (CPSFun {_} {τ′} {τ} {τ₂} {τ₃} e₁) v c)}
             {.(λ k → e₂)}
             (βVal𝑐 {τ = τ} {τ′ = τ′} {τ₁ = .τ₁} {τ₂ = .τ₂} {τ₃ = .τ₃}
                    {e₁ = e₁} {v = v} {c = c} {e₂ = e₂} sub) =
  begin
    dsMain𝑐 τ₁ τ₂ τ₃ (λ k → CPSApp (CPSFun e₁) v c)
  ≡⟨ refl ⟩
    Root
      (λ k → NonVal (dsC𝑐 τ′ τ₂ τ₃ τ₂ c)
             (App (Fun (dsT τ′) (dsT τ) (λ x → Root (λ k′ → dsE𝑐 τ₃ τ₂ (e₁ x k′))))
                  (dsV𝑐 τ v)))
  ⟶⟨ βVal {!!} ⟩
    Root (λ k → dsE𝑐 τ₃ τ₂ e₂)
  ≡⟨ refl ⟩
    dsMain𝑐 τ₁ τ₂ τ₃ (λ k → e₂)
  ∎

correctTerm𝑘 : {var : typ𝑘 → Set} → {τ₃ τ₅ : cpstyp} → 
               (e  : cpsterm𝑐[ var ∘ dsT ] (τ₅ ⇒ τ₅) τ₃) →
               (e′ : cpsterm𝑐[ var ∘ dsT ] (τ₅ ⇒ τ₅) τ₃) →
               cpsReduce e e′ → 
               ReduceTerm𝑘 {var} (dsE𝑐 τ₃ τ₅ e)
                                 (dsE𝑐 τ₃ τ₅ e′)
correctTerm𝑘 = {!!}

correctTermId𝑘 : {var : typ𝑘 → Set} → {τ₃ τ₅ : cpstyp} → 
                 (e  : cpsterm𝑐[ var ∘ dsT ] (τ₅ ⇒ τ₅) τ₃) →
                 (e′ : cpsterm𝑐[ var ∘ dsT ] (τ₅ ⇒ τ₅) τ₃) →
                 cpsReduce e e′ → 
                 ReduceTerm𝑘 {var}
                   (NonVal Hole (Reset (dsT τ₅) (dsT τ₃) (dsT τ₃)
                     (dsE𝑐 τ₃ τ₅ e)))
                   (NonVal Hole (Reset (dsT τ₅) (dsT τ₃) (dsT τ₃)
                     (dsE𝑐 τ₃ τ₅ e′)))
correctTermId𝑘 = {!!}


correctVal𝑘 : {var : typ𝑘 → Set} → {τ₁ : cpstyp} →
              {v  : cpsvalue𝑐[ var ∘ dsT ] τ₁} →
              {v′ : cpsvalue𝑐[ var ∘ dsT ] τ₁} →
              cpsReduceV v v′ →
              ReduceVal𝑘 {var} (dsV𝑐 τ₁ v) (dsV𝑐 τ₁ v′)
correctVal𝑘 = {!!}

correctCon𝑘 : {var : typ𝑘 → Set} → {τ₁ τ₂ τ₃ τ₅ : cpstyp} →
              {k  : cpscont𝑐[ var ∘ dsT ] (τ₅ ⇒ τ₅) (τ₁ ⇒ τ₂)} →
              {k′ : cpscont𝑐[ var ∘ dsT ] (τ₅ ⇒ τ₅) (τ₁ ⇒ τ₂)} →
              cpsReduceK k k′ →
              ReduceCon𝑘 {var} (dsC𝑐 τ₁ τ₂ τ₃ τ₅ k)
                               (dsC𝑐 τ₁ τ₂ τ₃ τ₅ k′)
correctCon𝑘 = {!!}
