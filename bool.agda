-- 足し算言語にif文を追加したもの

module bool where

open import Relation.Binary.PropositionalEquality
open import Data.Nat
-- open import Data.Bool

-- type
data typ : Set where
  Nat  : typ
  Bool : typ
  
-- source term
mutual
  data value : typ → Set where
    Num   : (n : ℕ) → value Nat
    True  : value Bool
    False : value Bool

  data term : typ → Set where
    Val : {τ : typ} → value τ → term τ
    Add : term Nat → term Nat → term Nat
    Eq  : {τ : typ} →  term τ → term τ → term Bool 
    If  : {τ : typ} → term Bool → term τ → term τ → term τ

-- frame
data frame[_] : typ → typ → Set where
  Add₁ : (e₂ : term Nat) →
         frame[ Nat ] Nat
  Add₂ : (v₁ : value Nat) →
         frame[ Nat ] Nat
  FEq   : {τ : typ} →
         (e₂ : term τ) →
         frame[ τ ] Bool
  FIf   : {τ : typ} →
         (e₁ : term τ) →
         (e₂ : term τ) →
         frame[ Bool ] τ

frame-plug : {τ₁ τ₂ : typ} →
             frame[ τ₂ ] τ₁ →
             term τ₂ →
             term τ₁
frame-plug (Add₁ e₂) e₁   = Add e₁ e₂
frame-plug (Add₂ v₁) e₂   = Add (Val v₁) e₂
frame-plug (FEq  e₂) e₁   = Eq e₁ e₂
frame-plug (FIf  e₁ e₂) b = If b e₁ e₂

-- reduction relation (= preservation)
data Reduce : {τ₁ : typ} →
     term τ₁ → term τ₁ → Set where
  RAdd      : {n₁ : ℕ} →
              {n₂ : ℕ} →
              {n  : ℕ} →
              n₁ + n₂ ≡ n →
              Reduce (Add (Val (Num n₁)) (Val (Num n₂))) (Val (Num n))
  REq-true  : {τ : typ} →
              {v₁ : value τ} →
              {v₂ : value τ} →
              v₁ ≡ v₂ →
              Reduce (Eq (Val v₁) (Val v₂)) (Val True)
  REq-false : {τ : typ} →
              {v₁ : value τ} →
              {v₂ : value τ} →
              v₁ ≢ v₂ →
              Reduce (Eq (Val v₁) (Val v₂)) (Val False)
  RIf-true  : {τ : typ} →
              {e₁ : term τ} →
              {e₂ : term τ} →
              Reduce (If (Val True) e₁ e₂) e₁   
  RIf-false : {τ : typ} →
              {e₁ : term τ} →
              {e₂ : term τ} →
              Reduce (If (Val False) e₁ e₂) e₂
  RFrame    : {τ₁ τ₂ : typ} →
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

-- equational reasoning
-- see ≡-Reasoning in Relation.Binary.PropositionalEquality.agda

infix  3 _∎
infixr 2 _⟶⟨_⟩_ _⟶*⟨_⟩_ _≡⟨_⟩_
infix  1 begin_

begin_ : {τ : typ} →
         {e₁ e₂ : term τ} → Reduce* e₁ e₂ → Reduce* e₁ e₂
begin_ red = red

_⟶⟨_⟩_ : {τ : typ} →
           (e₁ {e₂ e₃} : term τ) → Reduce e₁ e₂ → Reduce* e₂ e₃ →
           Reduce* e₁ e₃
_⟶⟨_⟩_ e₁ {e₂} {e₃} e₁-red-e₂ e₂-red*-e₃ =
  R*Trans e₁ e₂ e₃ e₁-red-e₂ e₂-red*-e₃

_⟶*⟨_⟩_ : {τ : typ} →
            (e₁ {e₂ e₃} : term τ) → Reduce* e₁ e₂ → Reduce* e₂ e₃ →
            Reduce* e₁ e₃
_⟶*⟨_⟩_ e₁ {.e₁} {e₃} (R*Id .e₁) e₁-red*-e₃ = e₁-red*-e₃
_⟶*⟨_⟩_ e₁ {.e₂} {e₃} (R*Trans .e₁ e₁′ e₂ e₁-red-e₁′ e₁′-red*-e₂) e₂-red*-e₃ =
  R*Trans e₁ e₁′ e₃ e₁-red-e₁′
          (e₁′ ⟶*⟨ e₁′-red*-e₂ ⟩ e₂-red*-e₃)

_≡⟨_⟩_ : {τ : typ} →
           (e₁ {e₂ e₃} : term τ) → e₁ ≡ e₂ → Reduce* e₂ e₃ →
           Reduce* e₁ e₃
_≡⟨_⟩_ e₁ {e₂} {e₃} refl e₂-red*-e₃ = e₂-red*-e₃

_∎ : {τ : typ} →
     (e : term τ) → Reduce* e e
_∎ e = R*Id e


------------------Proof1-------------------------

term1 : term Nat
term1 = Val (Num 1)

term2 : term Nat
term2 = Val (Num 2)

term0 : term Nat
term0 = Val (Num 0)

-- if true then 1 else 0
termif : term Nat
termif = If (Val (True)) term1 term0

-- if true then 1 else 0 ⟶ 1
test1 : Reduce* termif term1
test1 =
  begin
    If (Val True) (Val (Num 1)) (Val (Num zero))
  ⟶⟨ RIf-true ⟩
    term1
  ∎

------------------Proof2-------------------------

-- if true then 1 + 1 else 0
termif2 : term Nat
termif2 = If (Val True) (Add term1 term1) term0

-- if true then 1 + 1 else 0 ⟶ 2
test2 : Reduce* termif2 (Val (Num 2))
test2 =
  begin
    If (Val True) (Add term1 term1) term0
  ⟶⟨ RIf-true ⟩
    Add term1 term1
  ⟶⟨ RAdd refl ⟩
    Val (Num 2)
  ∎

------------------Proof3-------------------------

-- 1 ≡ 1 ⟶ true
test3 : Reduce* (Eq term1 term1) (Val True)
test3 =
  begin
    Eq (Val (Num 1)) (Val (Num 1))
  ⟶⟨ REq-true refl ⟩
    Val True
  ∎

-- 1 ≡ 2 ⟶ false
test4 : Reduce* (Eq term1 term2) (Val False)
test4 =
  begin
    Eq term1 term2
  ⟶⟨ REq-false (λ ()) ⟩
    Val False
  ∎

-- 1 + 1 ≡ 2 → true
test5 : Reduce* (Eq (Add term1 term1) term2) (Val True)
test5 =
  begin
    Eq (Add term1 term1) term2
  ⟶⟨ RFrame (FEq (Val (Num 2))) (RAdd refl) ⟩
    frame-plug (FEq (Val (Num 2))) (Val (Num (1 + 1)))
  ⟶⟨ REq-true refl ⟩
    Val True
  ∎

-- if 1 = 1 then 1 else 0 ⟶ 1
test6 : Reduce* (If (Eq term1 term1) term1 term0) term1
test6 =
  begin
    If (Eq term1 term1) term1 term0
  ⟶⟨ RFrame (FIf term1 term0) (REq-true refl) ⟩
    frame-plug (FIf term1 term0) (Val True)
  ⟶⟨ RIf-true ⟩
    term1
  ∎

-- if 1 = 2 then 1 else 0 ⟶ 0
test7 : Reduce* (If (Eq term1 term2) term1 term0) term0
test7 =
  begin
    If (Eq term1 term2) term1 term0
  ⟶⟨ RFrame (FIf term1 term0) (REq-false (λ ())) ⟩
    frame-plug (FIf term1 term0) (Val False)
  ⟶⟨ RIf-false ⟩
    term0
  ∎

-- -- 1 + 1 ≡ 1 + 1 ⟶ true
-- test6 : Reduce* (Eq (Add term1 term1) (Add term1 term1)) (Val True)
-- test6 =
--   begin
--     Eq (Add term1 term1) (Add term1 term1)
--   ⟶⟨ RFrame (FEq (Add term1 term1)) (RAdd refl) ⟩
--     frame-plug (FEq (Add term1 term1)) (Val (Num (1 + 1)))
--   ⟶⟨ {!!} ⟩
--     {!!}
--   ∎

