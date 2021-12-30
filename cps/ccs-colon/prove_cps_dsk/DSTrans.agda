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
dsT (τ₂ ⇒[ τ₁ ⇒ τ₃ ]⇒ τ₄) = (dsT τ₂) ⇒ (dsT τ₁) cps[ (dsT τ₃) , (dsT τ₄) ]

-- dsT𝑐 : ∀ (τ : cpstyp) → conttyp → typ𝑘
-- dsT𝑐 τ (τ₁ ⇒ τ₂) = (dsT τ₁) ⇒ (dsT τ₂) cps[ dsT τ , dsT τ ]

-- DS transformation to source term

mutual
  dsMain𝑐 : (τ₁ τ₂ τ₃ : cpstyp) → {var : typ𝑘 → Set} →
            ((var ∘ dsT) (τ₁ ⇒[ τ₂ ⇒ τ₂ ]⇒ τ₂) → cpsterm𝑐[ var ∘ dsT ] (τ₂ ⇒ τ₂) τ₃) →
            root𝑘[ var ] dsT τ₁ cps[ dsT τ₂ , dsT τ₃ ]
            -- term𝑘[ var ] dsT τ₁ cps[ dsT τ₂ , dsT τ₃ ]
  dsMain𝑐 τ₁ τ₂ τ₃ e = Root (λ k → dsE𝑐 τ₃ τ₂ (e k))

  dsV𝑐 : (τ₁ : cpstyp) → {var : typ𝑘 → Set} →
         cpsvalue𝑐[ var ∘ dsT ] τ₁ →
         value𝑘[ var ] (dsT τ₁) cps[τ,τ]       
  dsV𝑐 τ₁  (CPSVar {τ₁ = .τ₁} v) = Var v
  dsV𝑐 .Nat (CPSNum n) = Num n
  dsV𝑐 .(τ₂ ⇒[ τ₁ ⇒ τ₃ ]⇒ τ₄) (CPSFun {τ₁ = τ₁} {τ₂ = τ₂} {τ₃ = τ₃} {τ₄ = τ₄} e) =
    Fun (dsT τ₁) (dsT τ₂) (λ x → dsMain𝑐 τ₁ τ₃ τ₄ (e x))
  dsV𝑐 .(((τ₁ ⇒[ τ₂ ⇒ τ₃ ]⇒ τ₃) ⇒[ τ₄ ⇒ τ₄ ]⇒ τ₅) ⇒[ τ₁ ⇒ τ₂ ]⇒ τ₅)
       (CPSShift {τ₁ = τ₁} {τ₂ = τ₂} {τ₃ = τ₃} {τ₄ = τ₄} {τ₅ = τ₅}) = Shift

  dsC𝑐 : (τ₁ τ₂ τ₃ τ₅ : cpstyp) → {var : typ𝑘 → Set} →
         cpscont𝑐[ var ∘ dsT ] (τ₅ ⇒ τ₅) τ₃ (τ₁ ⇒ τ₂) →
         pcontext𝑘[ var , dsT τ₁ cps[ dsT τ₂ , dsT τ₃ ]] dsT τ₅
                 cps[ dsT τ₅ , dsT τ₃ ]
  dsC𝑐 τ₁ τ₂ τ₃ .τ₂  (CPSKVar {τ₁ = .τ₁} {τ₂ = .τ₂} k) = KHole k
  dsC𝑐 τ₁ .τ₁ τ₃ .τ₁ (CPSId {τ₁ = .τ₁}) = Hole
  dsC𝑐 τ₁ τ₂ τ₃ τ₅   (CPSCont {τ₁ = .τ₁} {τ₂ = .τ₂} {τ₄ = .τ₅} e) =
    KLet (λ x → dsE𝑐 τ₂ τ₅ (e x))
  
  dsE𝑐 : (τ₃ τ₅ : cpstyp) → {var : typ𝑘 → Set} →
         cpsterm𝑐[ var ∘ dsT ] (τ₅ ⇒ τ₅) τ₃ →
         term𝑘[ var ] dsT τ₅ cps[ dsT τ₅ , dsT τ₃ ]
  dsE𝑐 τ₃ τ₅ (CPSRet {τ₁ = τ₁} {τ₂ = .τ₃} {τ₃ = .τ₅} k v) =
    Val (dsC𝑐 τ₁ τ₃ τ₃ τ₅ k) (dsV𝑐 τ₁ v)
  dsE𝑐 τ₃ τ₅ (CPSApp {τ₁ = τ₁} {τ₂ = τ₂} {τ₃ = τ₄} {τ₄ = .τ₃} {τ₅ = .τ₅} v w k) =
    NonVal (dsC𝑐 τ₁ τ₄ τ₃ τ₅ k)
           (App (dsV𝑐 (τ₂ ⇒[ τ₁ ⇒ τ₄ ]⇒ τ₃) v) (dsV𝑐 τ₂ w))
  dsE𝑐 τ₃ τ₅ (CPSRetE {τ₀ = τ₀} {τ₁ = τ₁} {τ₂ = .τ₃} {τ₃ = .τ₅} k e) =
    NonVal (dsC𝑐 τ₁ τ₃ τ₃ τ₅ k)
           (Reset (dsT τ₀) (dsT τ₁) (dsT τ₃) (dsE𝑐 τ₁ τ₀ e))

  
