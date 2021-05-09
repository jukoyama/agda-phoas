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
    Fun (dsT τ₁) (dsT τ₂) λ x → {!Val!}
  dsV𝑐 .(((τ₁ ⇒[ τ₂ ⇒ τ₃ ]⇒ τ₃) ⇒[ τ₄ ⇒ τ₄ ]⇒ τ₅) ⇒[ τ₁ ⇒ τ₂ ]⇒ τ₅)
       (CPSShift {τ₁ = τ₁} {τ₂ = τ₂} {τ₃ = τ₃} {τ₄ = τ₄} {τ₅ = τ₅}) = Shift

  dsC𝑐 : (τ₁ τ₂ τ₃ : cpstyp) → {var : typ → Set} {cvar : conttyp → Set} →
         cpscont𝑐[ var ∘ dsT , cvar ] (τ₁ ⇒ τ₂) →
         pcontext[ var , dsT τ₁ cps[ dsT τ₂ , dsT τ₃ ]] dsT τ₁
                 cps[ dsT τ₂ , dsT τ₃ ]
  dsC𝑐 τ₁ τ₂  τ₃ (CPSKVar k) = Hole
  dsC𝑐 τ₁ .τ₁ τ₃ CPSId       = Hole
  dsC𝑐 τ₁ τ₂  τ₃ (CPSCont e) = Frame (Let λ x → {!dsE𝑐 ? ? ? ? (e x)!}) Hole


  dsE𝑐 : (τ₁ τ₂ τ₃ τ₄ : cpstyp) → {var : typ → Set} {cvar : conttyp → Set} →
         cpsterm𝑐[ var ∘ dsT , cvar ] τ₃ →
         term[ var ] dsT τ₁ cps[ dsT τ₂ , dsT τ₃ ]
  dsE𝑐 τ₁ τ₂ τ₃ τ₄ (CPSRet k v) =
      pcontext-plug (dsC𝑐 {!!} {!!} {!!} k) (Val (dsV𝑐 {!!} v))
  dsE𝑐 τ₁ τ₂ τ₃ τ₄ (CPSApp v w k) =
      pcontext-plug (dsC𝑐 {!!} {!!} {!!} k)
                  (NonVal (App (Val (dsV𝑐 {!!} v)) (Val (dsV𝑐 {!!} w))))
  dsE𝑐 τ₁ τ₂ τ₃ τ₄ (CPSRetE k e) =
      pcontext-plug (dsC𝑐 {!!} {!!} {!!} k)
                    (NonVal (Reset {!!} {!!} {!!} (dsE𝑐 {!!} {!!} {!!} {!!} e)))

  dsEMain𝑐 : (τ₁ τ₂ τ₃ α β : cpstyp) → {var : typ → Set} {cvar : conttyp → Set} →
             (cvar (α ⇒ β) → cpsterm𝑐[ var ∘ dsT , cvar ] {!!}) → 
             term[ var ] (dsT τ₁) cps[ dsT τ₂ , dsT τ₃ ]
  dsEMain𝑐 τ₁ τ₂ τ₃ α β e = NonVal (App (Val (Fun (dsT τ₁) {!!} (λ k → ?))) {!!})
