module DSTrans where

open import DStermK
open import CPSterm

open import Data.Unit
open import Data.Empty
open import Data.Nat
open import Function
open import Relation.Binary.PropositionalEquality

dsT : cpstyp → typ𝑘
dsT Nat = Nat
dsT Boolean = Boolean
dsT (τ₂ ⇒[ τ₁ ⇒ τ₃ ]⇒ τ₄) = dsT τ₂ ⇒ dsT τ₁ cps[ dsT τ₃ , dsT τ₄ ]

dsT𝑐 : conttyp → typ𝑘𝑐
dsT𝑐 (τ₂ ⇒ τ₁) = dsT τ₂ ▷ dsT τ₁

-- DS transformation to source term
mutual
  dsV𝑐 : {var : typ𝑘 → Set} {cvar : typ𝑘𝑐 → Set} → {τ₁ : cpstyp} →
         cpsvalue𝑐[ var ∘ dsT , cvar ∘ dsT𝑐 ] τ₁ →
         value𝑘[ var , cvar ] (dsT τ₁) cps[τ,τ]
  dsV𝑐 (CPSVar x) = Var x
  dsV𝑐 (CPSNum n) = Num n
  dsV𝑐 (CPSFun e) = Fun (λ x k → dsE𝑐 (e x k))
  dsV𝑐 CPSShift = Shift

  dsE𝑐 : {var : typ𝑘 → Set} {cvar : typ𝑘𝑐 → Set} → {τ : cpstyp} →
         cpsterm𝑐[ var ∘ dsT , cvar ∘ dsT𝑐 ] τ →
         term𝑘[ var , cvar ] dsT τ
  dsE𝑐 (CPSRet k v) = Ret (dsC𝑐 k) (dsV𝑐 v)
  dsE𝑐 (CPSApp v w k) = App (dsV𝑐 v) (dsV𝑐 w) (dsC𝑐 k)
  dsE𝑐 (CPSRetE k e) = RetE (dsC𝑐 k) (dsE𝑐 e)

  dsC𝑐 : {var : typ𝑘 → Set} {cvar : typ𝑘𝑐 → Set} → {τ₁ τ₂ : cpstyp} →
         cpscont𝑐[ var ∘ dsT , cvar ∘ dsT𝑐 ] (τ₁ ⇒ τ₂) →
         pcontext𝑘[ var , cvar ] (dsT τ₁ ▷ dsT τ₂)
  dsC𝑐 (CPSKVar k) = KHole k
  dsC𝑐 CPSId = Hole
  dsC𝑐 (CPSCont e) = KLet (λ x → dsE𝑐 (e x))
