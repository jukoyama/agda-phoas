-- Boolを追加したものを自動証明する

module bool-macro where

open import Data.Nat
open import Data.Unit using (⊤; tt)
open import Reflection using (newMeta)
open import Agda.Builtin.List using (List; _∷_; [])
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Agda.Builtin.Reflection renaming (bindTC to _>>=_)

-- デバッグ用のマクロ
macro
  showGoal : Term → TC ⊤
  showGoal hole = do
    type ← inferType hole
    t    ← quoteTC type
    typeError (termErr t ∷ [])

macro
  showCtx : Term → TC ⊤
  showCtx hole = do
    ctx ← getContext
    t   ← quoteTC ctx
    typeError (termErr t ∷ [])

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

-- 自動証明用のマクロ

{- 𝓋isible 𝓇elevant 𝒶rgument -}
vra : {A : Set} → A → Arg A
vra = arg (arg-info visible relevant)

counter-reduce : (n : ℕ) → (hole : Term) → TC ⊤
counter-reduce zero hole    = typeError (strErr "time out" ∷ [])
counter-reduce (suc n) hole = inferType hole >>=
  λ { (def (quote Reduce*) args) →
      newMeta unknown >>= λ m₁ →
      newMeta unknown >>= λ m₂ →
      newMeta unknown >>= λ m₃ →
      newMeta unknown >>= λ m₄ →
      newMeta unknown >>= λ m₅ →
      newMeta unknown >>= λ m₆ →
      unify hole (def (quote begin_) (vra (def (quote _⟶⟨_⟩_)
                                               (vra m₁
                                               ∷ vra m₂
                                               ∷ vra m₃
                                               ∷ []))
                                        ∷ [])) >>= λ _ →
      catchTC
        (unify m₃ (def (quote _∎) (vra m₄ ∷ [])) >>= λ _ →
         counter-reduce n m₂)
        (unify m₃ (def (quote _⟶⟨_⟩_)
                       (vra m₄ ∷ vra m₅ ∷ vra m₆ ∷ [])) >>= λ _ →
         counter-reduce n m₂ >>= λ _ →
         counter-reduce n m₃)
     ; (def (quote Reduce) args) → {!!}
     ; t → typeError (strErr "not a reduction" ∷ [])
     }
     
-- -- 再帰して停止するために関数counter-reduceを別に定義
-- macro
--   runTC : (hole : Term) → TC ⊤
--   runTC hole = counter_reduce 10 hole
