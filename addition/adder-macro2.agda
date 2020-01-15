-- adder-macro をもう少し綺麗に書くことを試みる

module adder-macro2 where

open import Data.Nat
open import Data.Unit using (⊤; tt)
open import Reflection using (newMeta)
open import Agda.Builtin.List using (List; _∷_; [])
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Agda.Builtin.Reflection renaming (bindTC to _>>=_)

-- UNUSED : いずれ使うかもしれないので残す
-- DELETE : 消す可能性が高いが一応残しておいているもの

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

-- 12
term12 : term Nat
term12 = Val (Num 12)

-- (3 + 5) + 4
term35-4 : term Nat
term35-4 = Add (Add term3 term5) term4

-- 4 + (3 + 5)
term4-35 : term Nat
term4-35 = Add term4 (Add term3 term5)

-----------------macro-------------------------

macro
    showGoal : Term → TC ⊤
    showGoal hole = do
        type ← inferType hole
        t ← quoteTC type
        typeError (termErr t ∷ [])

macro
    showCtx : Term → TC ⊤
    showCtx hole = do
        ctx ← getContext
        t   ← quoteTC ctx
        typeError (termErr t ∷ [])

{- 𝓋isible 𝓇elevant 𝒶rgument -}
vra : {A : Set} → A → Arg A
vra = arg (arg-info visible relevant)

{- 𝒽idden 𝓇elevant 𝒶rgument -}
hra : {A : Set} → A → Arg A
hra = arg (arg-info hidden relevant)

-- hole の数を受け取ったらその数だけの hole を List (Arg Term) の形で返す
create-multi-meta : (n : ℕ) → TC (List (Arg Term))
create-multi-meta zero    = returnTC []
create-multi-meta (suc n) =
  newMeta unknown >>= λ m →
  create-multi-meta n >>= λ rest →
  returnTC (vra m ∷ rest)

-- hole の数と コンストラクタの名前(?) を受け取ったら、hole を TC (List (Arg Term)) の形で返す
create-meta-con : (n : ℕ) → (consName : Name) → (hole : Term) → TC (List (Arg Term))
create-meta-con n consName hole =
  create-multi-meta n >>= λ ms →
  unify hole (con consName ms) >>= λ _ →
  returnTC ms

-- hole の数と コンストラクタの名前(?) を受け取ったら、hole を TC (List (Arg Term)) の形で返す
create-meta-def : (n : ℕ) → (consName : Name) → (hole : Term) → TC (List (Arg Term))
create-meta-def n consName hole =
  create-multi-meta n >>= λ ms →
  unify hole (def consName ms) >>= λ _ →
  returnTC ms

-- TC (List (Arg Term)) を hole に入れられるような形に使うためのもの
list-to-TC : (goal : List (Arg Term)) → TC ⊤
list-to-TC []                         = returnTC tt
list-to-TC (arg _ currentgoal ∷ rest) = list-to-TC rest

unify-arrow : (goal-list : List (Arg Term)) → TC (List (Arg Term))
unify-arrow []                    = returnTC []
unify-arrow (arg _ x ∷ goal-list) =
  create-meta-def 3 (quote _⟶⟨_⟩_) x

unify-qed : (hole : Term) → TC ⊤
unify-qed hole =
  create-meta-def 1 (quote _∎) hole >>= λ ms →
  list-to-TC ms

unify-begin⟶ : (hole : Term) → TC (List (Arg Term))
unify-begin⟶ hole =
  create-meta-def 1 (quote begin_) hole >>= λ l₁ →
  unify-arrow l₁

unify-Add₁ : (hole : Term) → TC Term
unify-Add₁ hole =
  create-meta-con 2 (quote RFrame) hole >>=
  λ { (arg _ x ∷ arg _ y ∷ []) →
       create-meta-con 1 (quote Add₁) x >>= λ _ →
       reduce y
     ; e → typeError (strErr "not correct list" ∷ [])
     }

unify-Add₂ : (hole : Term) → TC Term
unify-Add₂ hole =
  create-meta-con 2 (quote RFrame) hole >>=
  λ { (arg _ x ∷ arg _ y ∷ []) →
      create-meta-con 1 (quote Add₂) x >>= λ _ →
      reduce y
     ; e → typeError (strErr "not correct list" ∷ []) 
     }

unify-RAdd : (hole : Term) → TC ⊤
unify-RAdd hole =
  create-meta-con 1 (quote RAdd) hole >>=
  -- >>= λ ms → list-to-TC ms
  λ { (arg _ x ∷ []) →
      create-meta-con 0 (quote refl) x >>= λ ms →
      list-to-TC ms
     ; e → typeError (strErr "not correct list" ∷ [])
     }

-- macro に counterをつけたもの
-- main の macro には自然数は引数に取れないのでこのような形にする
counter-reduce : (n : ℕ) → (hole : Term) → TC ⊤
counter-reduce zero    hole = typeError (strErr "time out" ∷ [])
counter-reduce (suc n) hole = inferType hole >>=
  λ {  (def (quote Reduce*) args) →
       unify-begin⟶ hole >>=
       λ {(arg _ m₁ ∷ arg _ m₂ ∷ arg _ m₃ ∷ []) →
           catchTC
           (unify-qed m₃ >>= λ _ → counter-reduce n m₂)
           (unify-arrow (vra m₃ ∷ []) >>= λ ms → list-to-TC ms >>= λ _ →
           counter-reduce n m₂ >>= λ _ →
           counter-reduce n m₃)
         ; e → typeError (strErr "uncorrect list" ∷ [])
         }
     ; (def (quote Reduce) (_ ∷ arg _ a ∷ _ ∷ []))
     → reduce a >>=
     λ { (con (quote Add) (arg _ x ∷ arg _ y ∷ []))
         → reduce x >>=
         λ { (con (quote Add) args) →
             unify-Add₁ hole >>= λ m₂ → counter-reduce n m₂
            ; (con (quote Val) _)
              → reduce y >>=
              λ { (con (quote Add) _) →
                  unify-Add₂ hole >>= λ m₂ → counter-reduce n m₂
                 ; (con (quote Val) _) →
                   unify-RAdd hole
                 ; t → typeError (strErr "not a Value" ∷ [])
                 }
            ; t → typeError (strErr "neither Add nor Val" ∷ [])
            }
        ; t → typeError (strErr "not an Add" ∷ [])
        }
      ; t → typeError (strErr "not reducetion" ∷ [])
      }

-- main macro
macro
  runTC : (hole : Term) → TC ⊤
  runTC hole = counter-reduce 10 hole


--------------------Test----------------------

-- 3 + 5 ⟶*  8
test1 : Reduce* (Add term3 term5) (Val (Num 8))
test1 = Add term3 term5 ⟶⟨ RAdd refl ⟩ Val (Num 8) ∎

-- (3 + 5) + 4 ⟶* 12
test2 : Reduce* (Add (Add (Val (Num 3)) (Val (Num 5))) (Val (Num 4)))
                (Val (Num 12))
test2 = Add (Add (Val (Num 3)) (Val (Num 5))) (Val (Num 4)) ⟶⟨
          RFrame (Add₁ (Val (Num 4))) (RAdd refl) ⟩
          Add (Val (Num 8)) (Val (Num 4)) ⟶⟨ RAdd refl ⟩ Val (Num 12) ∎

-- 4 + (3 + 5) ⟶* 12
test3 : Reduce* term4-35 term12
test3 = term4-35 ⟶⟨ RFrame (Add₂ (Num 4)) (RAdd refl) ⟩
          Add (Val (Num 4)) (Val (Num 8)) ⟶⟨ RAdd refl ⟩ term12 ∎

-- (2 + 4) + (3 + 5) ⟶* 14
test4 : Reduce* (Add (Add (Val (Num 2)) (Val (Num 4))) (Add term3 term5)) (Val (Num 14))
test4 = Add (Add (Val (Num 2)) (Val (Num 4))) (Add term3 term5) ⟶⟨
          RFrame (Add₁ (Add term3 term5)) (RAdd refl) ⟩
          Add (Val (Num 6)) (Add term3 term5) ⟶⟨
          RFrame (Add₂ (Num 6)) (RAdd refl) ⟩
          Add (Val (Num 6)) (Val (Num 8)) ⟶⟨ RAdd refl ⟩ Val (Num 14) ∎

-- 1 + (2 + 3) + 4 ⟶* 10
test5 : Reduce* (Add term1 (Add (Add term2 term3) term4)) (Val (Num 10))
test5 = Add term1 (Add (Add term2 term3) term4) ⟶⟨
          RFrame (Add₂ (Num 1)) (RFrame (Add₁ term4) (RAdd refl)) ⟩
          Add (Val (Num 1)) (Add (Val (Num 5)) term4) ⟶⟨
          RFrame (Add₂ (Num 1)) (RAdd refl) ⟩
          Add (Val (Num 1)) (Val (Num 9)) ⟶⟨ RAdd refl ⟩ Val (Num 10) ∎
