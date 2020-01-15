-- Equational Reasoning を使って足し算を証明する

module adder-eq where

-- open import Agda.Builtin.Reflection
open import Agda.Builtin.Reflection renaming (bindTC to _>>=_)
open import Relation.Binary.PropositionalEquality
open import Data.Nat
open import Agda.Builtin.List using (_∷_; [])
open import Data.Unit using (⊤; tt)

macro
    unify-zero : (hole : Term) → TC ⊤
    unify-zero hole = inferType hole >>=
      λ{ (def (quote ℕ) []) → unify hole (lit (nat 0))
       ; t → typeError (strErr "not a number!" ∷ [])}

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

------------------NumDefine-------------------------

-- 1
term1 : term Nat
term1 = Val (Num 1)

-- 2
term2 : term Nat
term2 = Val (Num 2)

-- 3
term3 : term Nat
term3 = Val (Num 3)

-- 4
term4 : term Nat
term4 = Val (Num 4)

-- 5
term5 : term Nat
term5 = Val (Num 5)

-- 10
term10 : term Nat
term10 = Val (Num 10)

--14
term14 : term Nat
term14 = Val (Num 14)

-- 12
term12 : term Nat
term12 = Val (Num 12)

-- (3 + 5) + 4
term35-4 : term Nat
term35-4 = Add (Add term3 term5) term4

-- 4 + (3 + 5)
term4-35 : term Nat
term4-35 = Add term4 (Add term3 term5)

-- (2 + 4) + (3 + 5)
term24-35 : term Nat
term24-35 = Add (Add term2 term4) (Add term3 term5)

------------------Proof1-------------------------

-- (3 + 5) + 4 →* 12
test1 : Reduce* term35-4 term12
test1 =
  begin
    Add (Add term3 term5) term4
  ⟶⟨ RFrame (Add₁ (Val (Num 4))) (RAdd refl) ⟩
    Add (Val (Num 8)) term4
  ⟶⟨ RAdd refl ⟩
    term12
  ∎

------------------Proof2-------------------------

-- 4 + (3 + 5) →* 12
test2 : Reduce* term4-35 term12
test2 =
  begin
    Add term4 (Add term3 term5)
  ⟶⟨ RFrame (Add₂ (Num 4)) (RAdd refl) ⟩
    Add term4 (Val (Num 8))
  ⟶⟨ RAdd refl ⟩
    term12
  ∎

------------------Proof3-------------------------

-- (2 + 4) + (3 + 5) →* 14
test3 : Reduce* term24-35 term14
test3 =
  begin
    Add (Add term2 term4) (Add term3 term5)
  ⟶⟨ RFrame (Add₁ ((Add term3 term5))) (RAdd refl) ⟩
    Add (Val (Num 6)) (Add term3 term5)
  ⟶⟨ RFrame (Add₂ ((Num 6))) (RAdd refl) ⟩
    Add (Val (Num 6)) (Val (Num 8))
  ⟶⟨ RAdd refl ⟩
    term14
  ∎

------------------Proof4-------------------------

-- (1 + 2) + 3 + 4
test4 : Reduce* (Add (Add (Add term1 term2) term3) term4) term10
test4 =
  begin
    (Add (Add (Add term1 term2) term3) term4)
    ⟶⟨ RFrame (Add₁ term4) (RFrame (Add₁ term3) (RAdd refl)) ⟩
    frame-plug (Add₁ term4)
      (frame-plug (Add₁ term3) (Val (Num (1 + 2))))
    ⟶⟨ RFrame (Add₁ term4) (RAdd refl) ⟩
      frame-plug (Add₁ term4) (Val (Num (1 + 2 + 3)))
    ⟶⟨ RAdd refl ⟩
      Val (Num (1 + 2 + 3 + 4))
    ≡⟨ refl ⟩
    term10
  ∎

------------------Proof5-------------------------

-- 1 + (2 + 3) + 4
test5 : Reduce* (Add term1 (Add (Add term2 term3) term4)) term10
test5 =
  begin
    Add term1 (Add (Add term2 term3) term4)
  ⟶⟨ RFrame (Add₂ (Num 1)) (RFrame (Add₁ term4) (RAdd refl)) ⟩
    Add term1 (Add (Val (Num 5)) term4)
  ⟶⟨ RFrame (Add₂ (Num 1)) (RAdd refl) ⟩
    Add term1 (Val (Num 9))
  ⟶⟨ RAdd refl ⟩
    term10
  ∎
