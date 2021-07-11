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

dsT𝑐 : ∀ (τ : cpstyp) → conttyp → typ𝑘
dsT𝑐 τ (τ₁ ⇒ τ₂) = (dsT τ₁) ⇒ (dsT τ₂) cps[ dsT τ , dsT τ ]

-- DS transformation to source term

mutual
  dsMain𝑐 : (τ₁ τ₂ τ₃ : cpstyp) → {var : typ𝑘 → Set} →
            (var (dsT𝑐 τ₂ (τ₁ ⇒ τ₂)) → cpsterm𝑐[ var ∘ dsT , (λ τ τ𝑐 → var (dsT𝑐 τ τ𝑐)) ] (τ₁ ⇒ τ₂) τ₃) →
            term𝑘[ var ] dsT τ₁ cps[ dsT τ₂ , dsT τ₃ ]
  dsMain𝑐 τ₁ τ₂ τ₃ e =
    NonVal Hole
      (App Shift (Fun (dsT τ₂) (dsT τ₁ ⇒ dsT τ₂ cps[ dsT τ₂ , dsT τ₂ ])
           (λ k → dsE𝑐 τ₃ τ₁ τ₂ (e k))))

  dsV𝑐 : (τ₁ : cpstyp) → {var : typ𝑘 → Set} →
         cpsvalue𝑐[ var ∘ dsT , (λ τ τ𝑐 → var (dsT𝑐 τ τ𝑐)) ] τ₁ →
         value𝑘[ var ] (dsT τ₁) cps[τ,τ]       
  dsV𝑐 τ₁  (CPSVar v) = Var v
  dsV𝑐 .Nat (CPSNum n) = Num n
  dsV𝑐 .(τ₂ ⇒[ τ₁ ⇒ τ₃ ]⇒ τ₄) (CPSFun {τ = τ} {τ₁ = τ₁} {τ₂ = τ₂} {τ₃ = τ₃} {τ₄ = τ₄} e) =
    Fun (dsT τ₁) (dsT τ₂)
        (λ x → NonVal Hole
               (App Shift
                    (Fun (dsT τ₃) (dsT τ₁ ⇒ dsT τ₃ cps[ dsT τ , dsT τ ]) (λ k → dsE𝑐 τ₄ τ₁ τ₃ (e x k)))))
  dsV𝑐 .(((τ₁ ⇒[ τ₂ ⇒ τ₃ ]⇒ τ₃) ⇒[ τ₄ ⇒ τ₄ ]⇒ τ₅) ⇒[ τ₁ ⇒ τ₂ ]⇒ τ₅)
       (CPSShift {τ₁ = τ₁} {τ₂ = τ₂} {τ₃ = τ₃} {τ₄ = τ₄} {τ₅ = τ₅}) = Shift

  dsC𝑐 : (τ₁ τ₂ τ₃ τ₄ τ₅ : cpstyp) → {var : typ𝑘 → Set} →
         cpscont𝑐[ var ∘ dsT , (λ v v₁ → var (dsT𝑐 v v₁)) ] (τ₄ ⇒ τ₅) (τ₁ ⇒ τ₂) →
         pcontext𝑘[ var , dsT τ₁ cps[ dsT τ₂ , dsT τ₃ ]] dsT τ₅
                 cps[ dsT τ₅ , dsT τ₃ ]
  dsC𝑐 τ₁ τ₂ τ₃ .τ₁ .τ₂ {var} (CPSKVar {τ₁ = .τ₁} {τ₂ = .τ₂} k) = Frame (App₂ (Var k)) Hole
  dsC𝑐 τ₁ .τ₁ τ₃ .τ₁ .τ₁ {var} (CPSId {τ₁ = .τ₁}) = Hole
  dsC𝑐 τ₁ τ₂ τ₃ τ₄ τ₅ {var} (CPSCont {τ₁ = .τ₁} {τ₂ = .τ₂} {τ₃ = .τ₄} {τ₄ = .τ₅} e) =
    Frame (Let (λ x → dsE𝑐 τ₂ τ₄ τ₅ (e x))) Hole

  dsE𝑐 : (τ₃ τ₄ τ₅ : cpstyp) → {var : typ𝑘 → Set} →
         cpsterm𝑐[ var ∘ dsT , (λ τ τ𝑐 → var (dsT𝑐 τ τ𝑐)) ] (τ₄ ⇒ τ₅) τ₃ →
         term𝑘[ var ] dsT τ₅ cps[ dsT τ₅ , dsT τ₃ ]

  dsE𝑐 τ₃ τ₄ τ₅ (CPSRet {τ₁ = τ₁} {τ₂ = .τ₃} {τ₃ = .τ₄} {τ₄ = .τ₅} k v) =
    Val (dsC𝑐 τ₁ τ₃ τ₃ τ₄ τ₅ k) (dsV𝑐 τ₁ v)
  dsE𝑐 τ₃ τ₄ τ₅ (CPSApp {τ₁ = τ₁} {τ₂ = τ₂} {τ₃ = τ₆} {τ₄ = .τ₃} {τ₅ = .τ₄} {τ₆ = .τ₅} v w k) =
    NonVal (dsC𝑐 τ₁ τ₆ τ₃ τ₄ τ₅ k)
           (App (dsV𝑐 (τ₂ ⇒[ τ₁ ⇒ τ₆ ]⇒ τ₃) v) (dsV𝑐 τ₂ w))
  dsE𝑐 τ₃ τ₄ τ₅ (CPSRetE {τ₀ = τ₀} {τ₁ = τ₁} {τ₂ = .τ₃} {τ₃ = .τ₄} {τ₄ = .τ₅} k e) =
    NonVal (dsC𝑐 τ₁ τ₃ τ₃ τ₄ τ₅ k)
           (Reset (dsT τ₀) (dsT τ₁) (dsT τ₃) (dsE𝑐 τ₁ τ₀ τ₀ e))
