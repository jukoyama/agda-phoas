{-# OPTIONS --rewriting #-}

module Lemma_Left_Inv where

open import DStermK hiding (_⇒_cps[_])
open import CPSterm
open import CPSIsm
open import DSTrans

open import Function
open import Relation.Binary.PropositionalEquality
open import Data.Product

open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

dsT∘cpsT𝑘≡id : (τ : typ𝑘) → dsT (cpsT𝑘 τ) ≡ τ
dsT∘cpsT𝑘≡id Nat = refl
dsT∘cpsT𝑘≡id Boolean = refl
dsT∘cpsT𝑘≡id (τ ⇒ τ₁ cps[ τ₂ , τ₃ ]) = begin
    dsT (cpsT𝑘 τ) ⇒ dsT (cpsT𝑘 τ₁) cps[ dsT (cpsT𝑘 τ₂) , dsT (cpsT𝑘 τ₃) ]
  ≡⟨ cong (λ x → x ⇒ dsT (cpsT𝑘 τ₁) cps[ dsT (cpsT𝑘 τ₂) , dsT (cpsT𝑘 τ₃) ])
          (dsT∘cpsT𝑘≡id τ) ⟩
    (τ ⇒ dsT (cpsT𝑘 τ₁) cps[ dsT (cpsT𝑘 τ₂) , dsT (cpsT𝑘 τ₃) ])
  ≡⟨ cong (λ x → τ ⇒ x cps[ dsT (cpsT𝑘 τ₂) , dsT (cpsT𝑘 τ₃) ])
          (dsT∘cpsT𝑘≡id τ₁) ⟩
    (τ ⇒ τ₁ cps[ dsT (cpsT𝑘 τ₂) , dsT (cpsT𝑘 τ₃) ])
  ≡⟨ cong (λ x → τ ⇒ τ₁ cps[ x , dsT (cpsT𝑘 τ₃) ])
          (dsT∘cpsT𝑘≡id τ₂) ⟩
    (τ ⇒ τ₁ cps[ τ₂ , dsT (cpsT𝑘 τ₃) ])
  ≡⟨ cong (λ x → τ ⇒ τ₁ cps[ τ₂ , x ])
          (dsT∘cpsT𝑘≡id τ₃) ⟩
    τ ⇒ τ₁ cps[ τ₂ , τ₃ ]
  ∎
  where open ≡-Reasoning

{-# REWRITE dsT∘cpsT𝑘≡id #-}
mutual
  Left-InvR : {var : typ𝑘 → Set} → {τ₁ τ₂ τ₃ : typ𝑘} →
              (r : root𝑘[ var ] τ₁ cps[ τ₂ , τ₃ ]) →
              r
              ≡
              dsMain𝑐 (cpsT𝑘 τ₁) (cpsT𝑘 τ₂) (cpsT𝑘 τ₃) (cpsMain𝑘 τ₁ τ₂ τ₃ r)
  Left-InvR {var} {τ₁} {τ₂} {τ₃} (Root e) =
    begin
      Root (λ k → e k)
    ≡⟨ cong Root {!!} ⟩
      Root (λ k → dsE𝑐 (cpsT𝑘 τ₃) (cpsT𝑘 τ₂) (cpsE𝑘 τ₃ τ₂ (e k)))
    ≡⟨ {!!} ⟩
      dsMain𝑐 (cpsT𝑘 τ₁) (cpsT𝑘 τ₂) (cpsT𝑘 τ₃) (cpsMain𝑘 τ₁ τ₂ τ₃ (Root (λ k → e k)))
    ∎
    where open ≡-Reasoning

  Left-InvE : {var : typ𝑘 → Set} → {τ₃ τ₅ : typ𝑘} →
              (e : term𝑘[ var ] τ₅ cps[ τ₅ , τ₃ ]) → 
              e
              ≡
              dsE𝑐 (cpsT𝑘 τ₃) (cpsT𝑘 τ₅) (cpsE𝑘 τ₃ τ₅ e)
  Left-InvE {var} {τ₃} {τ₅} (Val {τ₁ = τ₁} {τ₂ = .τ₃} {τ₄ = .τ₅} k v) =
    begin
      Val k v
    ≡⟨ cong₂ Val (Left-InvC k) (Left-InvV v) ⟩
      Val (dsC𝑐 (cpsT𝑘 τ₁) (cpsT𝑘 τ₃) (cpsT𝑘 τ₃) (cpsT𝑘 τ₅)
                (cpsC𝑘 τ₁ τ₃ τ₃ τ₅ k))
          (dsV𝑐 (cpsT𝑘 τ₁) (cpsV𝑘 τ₁ v))
    ≡⟨ refl ⟩
      dsE𝑐 (cpsT𝑘 τ₃) (cpsT𝑘 τ₅)
           (CPSRet (cpsC𝑘 τ₁ τ₃ τ₃ τ₅ k)
                   (cpsV𝑘 τ₁ v))
    ≡⟨ refl ⟩
      dsE𝑐 (cpsT𝑘 τ₃) (cpsT𝑘 τ₅) (cpsE𝑘 τ₃ τ₅ (Val k v))
    ∎
    where open ≡-Reasoning

  Left-InvE {var} {τ₃} {τ₅}
            (NonVal {τ₁ = τ₁} {τ₂ = τ₂} {τ₃ = .τ₃} {τ₄ = .τ₅}
                    k
                    (App {τ₁ = .τ₁} {τ₂ = τ₄} {τ₃ = .τ₂} {τ₄ = .τ₃}
                         v w)) =
    begin
      NonVal k (App v w)
    ≡⟨ cong₂ NonVal (Left-InvC k) (cong₂ App (Left-InvV v) (Left-InvV w)) ⟩
      NonVal
        (dsC𝑐 (cpsT𝑘 τ₁) (cpsT𝑘 τ₂) (cpsT𝑘 τ₃) (cpsT𝑘 τ₅)
              (cpsC𝑘 τ₁ τ₂ τ₃ τ₅ k))
        (App (dsV𝑐 (cpsT𝑘 (τ₄ ⇒ τ₁ cps[ τ₂ , τ₃ ]))
             (cpsV𝑘 (τ₄ ⇒ τ₁ cps[ τ₂ , τ₃ ]) v))
             (dsV𝑐 (cpsT𝑘 τ₄) (cpsV𝑘 τ₄ w)))
    ≡⟨ refl ⟩
      dsE𝑐 (cpsT𝑘 τ₃) (cpsT𝑘 τ₅) (cpsE𝑘 τ₃ τ₅ (NonVal k (App v w)))
    ∎
    where open ≡-Reasoning

  Left-InvE {var} {τ₃} {τ₅}
            (NonVal {τ₁ = τ₁} {τ₂ = .τ₃} {τ₃ = .τ₃} {τ₄ = .τ₅}
                    k (Reset τ₂ .τ₁ .τ₃ e)) =
    begin
      NonVal k (Reset τ₂ τ₁ τ₃ e)
    ≡⟨ cong₂ NonVal (Left-InvC k)
             (cong (Reset τ₂ τ₁ τ₃) (Left-InvE e)) ⟩
      NonVal
        (dsC𝑐 (cpsT𝑘 τ₁) (cpsT𝑘 τ₃) (cpsT𝑘 τ₃) (cpsT𝑘 τ₅)
              (cpsC𝑘 τ₁ τ₃ τ₃ τ₅ k))
              (Reset τ₂ τ₁ τ₃ (dsE𝑐 (cpsT𝑘 τ₁) (cpsT𝑘 τ₂) (cpsE𝑘 τ₁ τ₂ e)))
    ≡⟨ refl ⟩
      dsE𝑐 (cpsT𝑘 τ₃) (cpsT𝑘 τ₅)
           (cpsE𝑘 τ₃ τ₅ (NonVal k (Reset τ₂ τ₁ τ₃ e)))
    ∎
    where open ≡-Reasoning

  Left-InvV : {var : typ𝑘 → Set} → {τ₁ : typ𝑘} →
              (v : value𝑘[ var ] τ₁ cps[τ,τ]) → 
              v
              ≡
              dsV𝑐 (cpsT𝑘 τ₁) (cpsV𝑘 τ₁ v)
  Left-InvV {var} {.Nat} (Num n) = refl
  Left-InvV {var} {τ₁} (Var {τ₁ = .τ₁} v) = refl
  Left-InvV {var} {.(τ₂ ⇒ τ₁ cps[ τ₃ , τ₄ ])}
            (Fun τ₁ τ₂ {τ₃ = τ₃} {τ₄ = τ₄} r) =
    begin
      Fun τ₁ τ₂ (λ x → r x)
    ≡⟨ cong (Fun τ₁ τ₂) {!!} ⟩
      Fun τ₁ τ₂ {!!}
    ≡⟨ {!!} ⟩
      dsV𝑐 (cpsT𝑘 (τ₂ ⇒ τ₁ cps[ τ₃ , τ₄ ]))
           (cpsV𝑘 (τ₂ ⇒ τ₁ cps[ τ₃ , τ₄ ]) (Fun τ₁ τ₂ (λ x → r x)))
    ∎
    where open ≡-Reasoning

  Left-InvV {var} {.(((τ₃ ⇒ τ₄ cps[ τ , τ ]) ⇒ τ₁ cps[ τ₁ , τ₂ ]) ⇒ τ₃ cps[ τ₄ , τ₂ ])}
            (Shift {τ = τ} {τ₁ = τ₁} {τ₂ = τ₂} {τ₃ = τ₃} {τ₄ = τ₄}) = refl

  Left-InvC : {var : typ𝑘 → Set} → {τ₁ τ₂ τ₃ τ₅ : typ𝑘} →
              (k : pcontext𝑘[ var , τ₁ cps[ τ₂ , τ₃ ]] τ₅
                           cps[ τ₅ , τ₃ ]) → 
              k
              ≡
              dsC𝑐 (cpsT𝑘 τ₁) (cpsT𝑘 τ₂) (cpsT𝑘 τ₃) (cpsT𝑘 τ₅)
                   (cpsC𝑘 τ₁ τ₂ τ₃ τ₅ k)
  Left-InvC {var} {τ₁} {τ₂} {τ₃} {.τ₂} (KHole {τ₁ = .τ₁} {τ₂ = .τ₂} {τ₃ = .τ₃} k) = refl
  Left-InvC {var} {τ₁} {.τ₁} {τ₃} {.τ₁} (Hole {τ₁ = .τ₁} {τ₃ = .τ₃}) = refl
  Left-InvC {var} {τ₁} {τ₂} {τ₃} {τ₅}
            (KLet {τ₁ = .τ₁} {τ₂ = .τ₅} {β = .τ₂} {γ = .τ₃} e₂) =
    begin
      KLet (λ x → e₂ x)
    ≡⟨ cong KLet {!!} ⟩
      dsC𝑐 (cpsT𝑘 τ₁) (cpsT𝑘 τ₂) (cpsT𝑘 τ₃) (cpsT𝑘 τ₅)
        (cpsC𝑘 τ₁ τ₂ τ₃ τ₅ (KLet e₂))
    ≡⟨ refl ⟩
      dsC𝑐 (cpsT𝑘 τ₁) (cpsT𝑘 τ₂) (cpsT𝑘 τ₃) (cpsT𝑘 τ₅)
           (cpsC𝑘 τ₁ τ₂ τ₃ τ₅ (KLet e₂))
    ∎
    where open ≡-Reasoning          
