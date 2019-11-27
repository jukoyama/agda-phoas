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
  R*Id    : {τ₁ : typ} →
            (e : term τ₁) →
            Reduce* e e
  R*Trans : {τ₁ : typ} →
            (e₁ : term τ₁) →
            (e₂ : term τ₁) →
            (e₃ : term τ₁) →
            Reduce e₁ e₂ →
            Reduce* e₂ e₃ →
            Reduce* e₁ e₃

------------------Proof1-------------------------

 -- Proof of A + B

-- 3
term3 : term Nat
term3 = Val (Num 3)

-- 5
term5 : term Nat
term5 = Val (Num 5)

-- 3 + 5
term35 : term Nat
term35 = Add term3 term5

-- 8
term8 : term Nat
term8 = Val (Num 8)

-- 3 + 5 ≡ 8
test1 : Reduce term35 term8
test1 = RAdd refl

------------------Proof2-------------------------

 -- Proof of (A + B) + C

-- 4
term4 : term Nat
term4 = Val (Num 4)

-- (3 + 5) + 4
term35-4 : term Nat
term35-4 = Add term35 term4

-- 8 + 4
term84 : term Nat
term84 = Add term8 term4

-- 12
term12 : term Nat
term12 = Val (Num 12)

-- (3 + 5) + 4 → 8 + 4
test2′ : Reduce term35-4 term84
test2′ = RFrame (Add₁ (Val (Num 4))) (RAdd refl)

-- 8 + 4 →  12
test2 : Reduce term84 term12
test2 = RAdd refl

------------------Proof3-------------------------

 -- Proof of (A + B) + C with multi steps

-- 8 + 4 →* 12
test3′ : Reduce* term84 term12
test3′ = R*Trans term84 term12 term12 test2 (R*Id term12)

-- (3 + 5) + 4 →* 12
test3 : Reduce* term35-4 term12
test3 = R*Trans term35-4 term84 term12 test2′ test3′

------------------Proof4-------------------------

 -- Proof of A + (B + C)

-- 4 + (3 + 5)
term4-35 : term Nat
term4-35 = Add term4 term35

-- 4 + 8
term48 : term Nat
term48 = Add term4 term8

-- 4 + (3 + 5) → 4 + 8
test4′ : Reduce term4-35 term48
test4′ = RFrame (Add₂ (Num 4)) (RAdd refl)

-- 4 + 8 → 12
test4 : Reduce term48 term12
test4 = RAdd refl

------------------Proof5-------------------------

 -- Proof of A + (B + C) with mutli steps

-- 4 + 8 →* 12
test5′ : Reduce* term48 term12
test5′ = R*Trans term48 term12 term12 test4 (R*Id term12) 

-- 4 + (3 + 5) →* 12
test5 : Reduce* term4-35 term12
test5 = R*Trans term4-35 term48 term12 test4′ test5′
