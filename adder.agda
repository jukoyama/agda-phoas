module adder where

open import Relation.Binary.PropositionalEquality
open import Data.Nat

-- type
data typ : Set where
  Nat : typ

-- source term
mutual
  data value : typ → Set where
    Num : (n : ℕ) → value Nat

  data term : typ → Set where
    Val : {τ₁ : typ} → value τ₁ → term τ₁
    Add : term Nat → term Nat → term Nat

-- frame
data frame[_] : typ → typ → Set where
  Add₁ : (e₂ : term Nat) →
         frame[ Nat ] Nat
  Add₂ : (v₁ : value Nat) →
         frame[ Nat ] Nat

frame-plug : {τ₁ τ₂ : typ} →
             frame[ τ₂ ] τ₁ →
             term τ₂ →
             term τ₁
frame-plug (Add₁ e₂) e₁ = Add e₁ e₂
frame-plug (Add₂ v₁) e₂ = Add (Val v₁) e₂

-- reduction relation (= preservation)
data Reduce : {τ₁ : typ} →
     term τ₁ → term τ₁ → Set where
  RAdd   : {n₁ : ℕ} →
           {n₂ : ℕ} →
           {n  : ℕ} →
           n₁ + n₂ ≡ n →
           Reduce (Add (Val (Num n₁)) (Val (Num n₂))) (Val (Num n))
  RFrame : {τ₁ τ₂ : typ} →
           {e : term τ₁} →
           {e′ : term τ₁} →
           (f : frame[ τ₁ ] τ₂) →
           Reduce e e′ →
           Reduce (frame-plug f e) (frame-plug f e′)

data Reduce* : {τ₁ : typ} →
     term τ₁ → term τ₁ → Set where
  R*Id  : {τ₁ : typ} →
           (e : term τ₁) →
           Reduce* e e
  R*Trans : {τ₁ : typ} →
           (e₁ : term τ₁) →
           (e₂ : term τ₁) →
           (e₃ : term τ₁) →
           Reduce e₁ e₂ →
           Reduce* e₂ e₃ →
           Reduce* e₁ e₃

term3 : term Nat
term3 = Val (Num 3)

term5 : term Nat
term5 = Val (Num 5)

term35 : term Nat
term35 = Add term3 term5

term8 : term Nat
term8 = Val (Num 8)

test1 : Reduce term35 term8
test1 = RAdd refl
