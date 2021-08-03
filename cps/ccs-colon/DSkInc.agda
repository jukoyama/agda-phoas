module DSkInc where

open import DSterm
open import DStermK

-- Inclusion in DS term of DS kernel term

open import Function

dsI : typ → typ𝑘
dsI Nat = Nat
dsI Boolean = Boolean
dsI (τ₂ ⇒ τ₁ cps[ τ₃ , τ₄ ]) = dsI τ₂ ⇒ dsI τ₁ cps[ dsI τ₃ , dsI τ₄ ]

mutual
  dsV𝑖 : (τ₁ : typ) → {var : typ𝑘 → Set} →
         value[ var ∘ dsI ] τ₁ cps[τ,τ] →
         value𝑘[ var ] dsI τ₁ cps[τ,τ]
  dsV𝑖 .Nat (Num n) = Num n
  dsV𝑖 τ₁  (Var v) = Var v
  dsV𝑖 .(τ₂ ⇒ τ₁ cps[ τ₃ , τ₄ ]) {var} (Fun τ₁ τ₂ {τ₃ = τ₃} {τ₄ = τ₄} e) =
    Fun (dsI τ₃) (dsI τ₁) (dsI τ₂)
        λ x k → dsE𝑖 τ₁ τ₃ τ₄ τ₃ (e x) {!!}
                     -- (Frame {τ = dsI τ₄} {dsI τ₁} {dsI τ₃} {dsI τ₁} {dsI τ₃} {dsI τ₃} {dsI τ₃} (App₂ (Var k)) Hole)
    -- Fun (dsI τ₃) (dsI τ₁) (dsI τ₂)
    --     λ x k → dsE𝑖 τ₁ τ₃ τ₄ τ₃ (e x)
    --                  (Frame {τ = dsI τ₄} {dsI τ₁} {dsI τ₃} {dsI τ₃} {dsI τ₃} (App₂ (Var k)) Hole)
  dsV𝑖 .(((τ₃ ⇒ τ₄ cps[ τ , τ ]) ⇒ τ₁ cps[ τ₁ , τ₂ ]) ⇒ τ₃ cps[ τ₄ , τ₂ ])
       (Shift {τ = τ} {τ₁ = τ₁} {τ₂ = τ₂} {τ₃ = τ₃} {τ₄ = τ₄}) = Shift

  dsE𝑖 : (τ₁ τ₂ τ₃ τ₄ : typ) → {var : typ𝑘 → Set} →
         term[ var ∘ dsI ] τ₁ cps[ τ₂ , τ₃ ] →
         pcontext𝑘[ var , dsI {!τ₁!} cps[ dsI {!τ₂!} , dsI {!τ₃!} ]] dsI τ₄ cps[ dsI τ₄ , dsI {!τ₃!} ] →
         term𝑘[ var ] dsI τ₄ cps[ dsI τ₄ , dsI τ₃ ]

  dsE𝑖 τ₁ τ₂ .τ₂ τ₄ {var} (Val {τ₁ = .τ₁} {τ₂ = .τ₂} v) k = {!!}


  dsE𝑖 τ₁ τ₂ τ₃ τ₄ {var} (NonVal {τ₁ = .τ₁} {τ₂ = .τ₂} {τ₃ = .τ₃}
       (App {τ₁ = .τ₁} {τ₂ = τ₅} {τ₃ = .τ₂} {τ₄ = .τ₃} {τ₅ = .τ₃} {τ₆ = .τ₃}
            (Val {τ₁ = .(τ₅ ⇒ τ₁ cps[ τ₂ , τ₃ ])} {τ₂ = .τ₃} v₁)
            (Val {τ₁ = .τ₅} {τ₂ = .τ₃} v₂))) k =
    NonVal {!k!} (App (dsV𝑖 (τ₅ ⇒ τ₁ cps[ τ₂ , τ₃ ]) v₁) (dsV𝑖 τ₅ v₂))
  
  dsE𝑖 τ₁ τ₂ τ₃ τ₄ {var} (NonVal {τ₁ = .τ₁} {τ₂ = .τ₂} {τ₃ = .τ₃}
       (App {τ₁ = .τ₁} {τ₂ = τ₅} {τ₃ = .τ₂} {τ₄ = τ₆} {τ₅ = .τ₆} {τ₆ = .τ₃}
            (NonVal {τ₁ = .(τ₅ ⇒ τ₁ cps[ τ₂ , τ₆ ])} {τ₂ = .τ₆} {τ₃ = .τ₃} e₁)
            (Val {τ₁ = .τ₅} {τ₂ = .τ₆} v₂))) k =
    dsE𝑖 (τ₅ ⇒ τ₁ cps[ τ₂ , τ₆ ]) τ₆ τ₃ τ₄ (NonVal e₁)
         (Frame (Let (λ m → NonVal k (App (Var m) (dsV𝑖 τ₅ v₂)))) Hole)
            
  dsE𝑖 τ₁ τ₂ τ₃ τ₄ {var} (NonVal {τ₁ = .τ₁} {τ₂ = .τ₂} {τ₃ = .τ₃}
       (App {τ₁ = .τ₁} {τ₂ = τ₅} {τ₃ = .τ₂} {τ₄ = τ₆} {τ₅ = .τ₃} {τ₆ = .τ₃}
            (Val {τ₁ = .(τ₅ ⇒ τ₁ cps[ τ₂ , τ₆ ])} {τ₂ = .τ₃} v₁)
            (NonVal {τ₁ = .τ₅} {τ₂ = .τ₆} {τ₃ = .τ₃} e₂))) k =
    dsE𝑖 τ₅ τ₆ τ₃ τ₄ (NonVal e₂)
         (Frame (Let (λ n → NonVal k (App (dsV𝑖 ({!!} ⇒ {!!} cps[ {!!} , {!!} ]) {!v₁!}) (Var n)))) Hole)

  dsE𝑖 τ₁ τ₂ τ₃ τ₄ {var} (NonVal {τ₁ = .τ₁} {τ₂ = .τ₂} {τ₃ = .τ₃}
       (App {τ₁ = .τ₁} {τ₂ = τ₅} {τ₃ = .τ₂} {τ₄ = τ₆} {τ₅ = τ₇} {τ₆ = .τ₃}
            (NonVal {τ₁ = .(τ₅ ⇒ τ₁ cps[ τ₂ , τ₆ ])} {τ₂ = .τ₇} {τ₃ = .τ₃} e₁)
            (NonVal {τ₁ = .τ₅} {τ₂ = .τ₆} {τ₃ = .τ₇} e₂))) k =
    dsE𝑖 (τ₅ ⇒ τ₁ cps[ τ₂ , τ₆ ]) τ₇ τ₃ τ₄ (NonVal e₁)
         (Frame (Let (λ m →
    dsE𝑖 τ₅ τ₆ τ₇ τ₄ (NonVal e₂)
         (Frame (Let (λ n → NonVal k (App (Var m) (Var n)))) Hole)))
         Hole)


  dsE𝑖 τ₁ τ₂ .τ₂ τ₄ {var} (NonVal {τ₁ = .τ₁} {τ₂ = .τ₂} {τ₃ = .τ₂} (Reset τ₃ .τ₁ .τ₂ x)) k = {!!}
  dsE𝑖 τ₁ τ₂ τ₃ τ₄ {var} (NonVal {τ₁ = .τ₁} {τ₂ = .τ₂} {τ₃ = .τ₃} (Let {τ₁ = τ₅} {τ₂ = .τ₁} {α = .τ₂} {β = β} {γ = .τ₃} x x₁)) k = {!!}
