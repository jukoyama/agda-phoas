module DSTrans where

open import DSterm
open import CPSterm
open import CPSColonTrans

open import Data.Unit
open import Data.Empty
open import Data.Nat
open import Function
open import Relation.Binary.PropositionalEquality

dsT : cpstyp → typ
dsT Nat = Nat
dsT Boolean = Boolean
dsT (τ₂ ⇒[ τ₁ ⇒ τ₃ ]⇒ τ₄) =
  (dsT τ₂) ⇒ (dsT τ₁) cps[ dsT τ₃ , dsT τ₄ ]

-- DS transformation to source term

mutual
  dsV𝑐 : (τ₁ : cpstyp) → {var : typ → Set} {cvar : conttyp → Set} →
         cpsvalue𝑐[ var ∘ dsT , cvar ] τ₁ →
         value[ var ] (dsT τ₁) cps[τ,τ]
  dsV𝑐 τ₁  (CPSVar v) = Var v
  dsV𝑐 .Nat (CPSNum n) = Num n
  dsV𝑐 .(τ₂ ⇒[ τ₁ ⇒ τ₃ ]⇒ τ₄)
       (CPSFun {τ₁ = τ₁} {τ₂ = τ₂} {τ₃ = τ₃} {τ₄ = τ₄} e) =
    Fun (dsT τ₁) (dsT τ₂) λ x → {!!}
  dsV𝑐 .(((τ₁ ⇒[ τ₂ ⇒ τ₃ ]⇒ τ₃) ⇒[ τ₄ ⇒ τ₄ ]⇒ τ₅) ⇒[ τ₁ ⇒ τ₂ ]⇒ τ₅)
       (CPSShift {τ₁ = τ₁} {τ₂ = τ₂} {τ₃ = τ₃} {τ₄ = τ₄} {τ₅ = τ₅}) = Shift

  dsC𝑐 : (τ₁ τ₂ τ₃ τ₄ τ₅ : cpstyp) → {var : typ → Set} {cvar : conttyp → Set} →
         cpscont𝑐[ var ∘ dsT , cvar ] (τ₅ ⇒ τ₄) (τ₁ ⇒ τ₂) →
         pcontext[ var , dsT τ₁ cps[ dsT τ₂ , dsT τ₃ ]] dsT τ₅
                 cps[ dsT τ₄ , dsT τ₃ ]
  dsC𝑐 τ₁ τ₂ τ₃ .τ₂ .τ₁ (CPSKVar k) = Hole
  dsC𝑐 τ₁ .τ₁ τ₃ .τ₁ .τ₁ CPSId = Hole
  dsC𝑐 τ₁ τ₂ τ₃ τ₄ τ₅ (CPSCont e) = Frame (Let (λ x → dsE𝑐 τ₅ τ₄ τ₂ (e x))) Hole

  dsE𝑐 : (τ₁ τ₂ τ₃ : cpstyp) → {var : typ → Set} {cvar : conttyp → Set} →
         cpsterm𝑐[ var ∘ dsT , cvar ] (τ₁ ⇒ τ₂) τ₃ →
         term[ var ] dsT τ₁ cps[ dsT τ₂ , dsT τ₃ ]
         
  dsE𝑐 τ₁ τ₂ τ₃ (CPSRet {τ₁ = .τ₃} {τ₂ = τ₆} {τ₃ = .τ₂} {τ₄ = .τ₁} k v) =
    pcontext-plug (dsC𝑐 τ₆ τ₃ τ₃ τ₂ τ₁ k) (Val (dsV𝑐 τ₆ v))
  dsE𝑐 τ₁ τ₂ τ₃ (CPSApp {τ₁ = τ₆} {τ₂ = τ₇} {τ₃ = τ₈} {τ₄ = .τ₃} {τ₅ = .τ₂} {τ₆ = .τ₁} v w k) =
    pcontext-plug (dsC𝑐 τ₆ τ₈ τ₃ τ₂ τ₁ k)
                  (NonVal (App (Val (dsV𝑐 (τ₇ ⇒[ τ₆ ⇒ τ₈ ]⇒ τ₃) v)) (Val (dsV𝑐 τ₇ w))))
  dsE𝑐 τ₁ τ₂ τ₃ (CPSRetE {τ₀ = τ₀} {τ₁ = .τ₃} {τ₂ = τ₆} {τ₃ = .τ₂} {τ₄ = .τ₁} k e) =
    pcontext-plug (dsC𝑐 τ₆ τ₃ τ₃ τ₂ τ₁ k)
                  (NonVal (Reset (dsT τ₀) (dsT τ₆) (dsT τ₃) (dsE𝑐 τ₀ τ₀ τ₆ e)))
