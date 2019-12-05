-- 足し算言語を macro を使って証明してみる

module adder-macro where

open import Data.Nat
open import Data.Unit using (⊤; tt)
open import Reflection using (newMeta)
open import Agda.Builtin.List using (List; _∷_; [])
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Agda.Builtin.Reflection renaming (bindTC to _>>=_)

-- macro
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

-----------------Proof1-------------------------

{- 𝓋isible 𝓇elevant 𝒶rgument -}
vra : {A : Set} → A → Arg A
vra = arg (arg-info visible relevant)

{- 𝒽idden 𝓇elevant 𝒶rgument -}
hra : {A : Set} → A → Arg A
hra = arg (arg-info hidden relevant)

-- (未使用)
-- hole の数を受け取ったらその数だけの hole を List (Arg Term) の形で返す
create-multi-meta : (n : ℕ) → TC (List (Arg Term))
create-multi-meta zero    = returnTC []
create-multi-meta (suc n) =
  newMeta unknown >>= λ m →
  create-multi-meta n >>= λ rest →
  returnTC (vra m ∷ rest)

-- (未使用)
-- hole の数と コンストラクタの名前(?) を受け取ったら、hole を TC (List (Arg Term)) の形で返す
create-meta-cons : (n : ℕ) → (consName : Name) → (hole : Term) → TC (List (Arg Term))
create-meta-cons n consName hole =
  create-multi-meta n >>= λ ms →
  unify hole (con consName ms) >>= λ _ →
  -- unify hole できているのか....?
  returnTC ms

-- (未使用)
-- TC (List (Arg Term)) を hole に入れられるような形に使うためのもの
list-to-TC : (goal : List (Arg Term)) → TC ⊤
list-to-TC []                         = returnTC tt
list-to-TC (arg _ currentgoal ∷ rest) = list-to-TC rest

-- Reduce の形が来たら RAdd にする (お試しで作ったもの)
-- macro
--   unify-reduce : (hole : Term) → TC ⊤
--   unify-reduce hole = inferType hole >>=
--     λ{ (def (quote Reduce)
--             (_ ∷ arg _ (con (quote Add) (_ ∷ _ ∷ []))  ∷ _ ∷ []))
--        → newMeta unknown >>= λ m
--        → unify hole (con (quote RAdd) (vra m ∷ []))

-- do記法で書いたもの
-- macro
--   unify-reduce : (hole : Term) → TC ⊤
--   unify-reduce hole = do
--     m ← newMeta unknown
--     (def (quote Reduce)
--          (_ ∷ arg _ (con (quote Add) (_ ∷ _ ∷ [])) ∷ _ ∷ [])) ← inferType hole
--        where unknown → typeError (strErr "not a number!" ∷ [])
--     unify hole (con (quote RAdd) (vra m ∷ []))

counter-reduce′ : (n : ℕ) → (hole : Term) → TC ⊤
counter-reduce′ zero    hole = typeError (strErr "time out" ∷ [])
counter-reduce′ (suc n) hole = inferType hole >>=
    λ { (def (quote Reduce)
              (_ ∷ arg _ a ∷ _ ∷ []))
              -- frame-plug の形になっている場合を考えて
              → reduce a >>=
              λ { (con (quote Add) (arg _ x ∷ arg _ y ∷ []))
                 --  term3 のような形になっているときのことを考えて
                 → reduce x >>=
                 λ { (con (quote Val) _) →
                    -- term3 のような形になっているときのことを考えて
                    reduce y >>=
                    -- Add ((value τ) (value τ)) のときは RAdd
                    λ { (con (quote Val) _) →
                       newMeta unknown >>= λ m →
                       -- DELETE : hole を作る関数を作ってみたがかえってわかりにくくなったのでいずれ消す
                       -- create-meta-cons 1 (quote RAdd) hole >>= λ ms →
                       -- list-to-TC ms
                       -- refl が入らないときは 穴を抜けられないのでこれ良さそう
                       unify hole (con (quote RAdd) (vra (con ((quote refl)) []) ∷ []))
                       -- Add ((value τ) (Add ...)) のときは Add₂
                       ; (con (quote Add) _) →
                       newMeta unknown >>= λ m₁ →
                       newMeta unknown >>= λ m₂ →
                       unify hole (con (quote RFrame) (vra (con (quote Add₂) (vra m₁ ∷ []))
                                                      ∷ vra m₂
                                                      ∷ [])) >>= λ _ →
                       counter-reduce′ n m₂
                       ; t → typeError (termErr y ∷ [])
                       }
                    -- Add ((Add ...) ...) のときは Add₁
                    ; (con (quote Add) _) →
                     newMeta unknown >>= λ m₁ →
                     newMeta unknown >>= λ m₂ →
                     unify hole (con (quote RFrame) (vra (con (quote Add₁) (vra m₁ ∷ []))
                                                    ∷ vra m₂
                                                    ∷ [])) >>= λ _ →
                     counter-reduce′ n m₂
                    ; t → typeError (strErr "unacceptable type" ∷ [])
                    }
                  ; t → typeError (strErr "Not Add type" ∷ []) 
                  }
             -- → reduce x >>= λ r
             -- → inferType hole >>= λ i
             -- → quoteTC i >> λ q
             -- → normalise x >>= λ n
             -- → typeError (termErr x ∷ [])
       ; (def (quote _≡_) _)
         → unify hole (con ((quote refl)) [])
       -- ; t → typeError (strErr "not a reduction" ∷ [])
       ; t →
         quoteTC t >>= λ q →
         typeError (termErr q ∷ [])
       }

-- DELETE : 必要なさそうなのでいずれ消す
-- 新しくできた hole を返す
return-subgoal : (hole : Term) → TC ⊤
return-subgoal hole = inferType hole >>=
  λ { (def (quote Reduce)
            (_ ∷ arg _ a ∷ _ ∷ [])) →
            reduce a >>=
            λ { (con (quote Add) (arg _ x ∷ arg _ y ∷ [])) →
               reduce x >>=
               λ { (con (quote Add) _) →
                   newMeta unknown >>= λ m₁ →
                   newMeta unknown >>= λ m₂ →
                   unify hole (con (quote RFrame) (vra (con (quote Add₁) (vra m₁ ∷ []))
                                                  ∷ vra m₂
                                                  ∷ [])) >>= λ _ →
                  returnTC tt
                  ; t → typeError (strErr "unknown type" ∷ [])
                  } 
               ; t → typeError (strErr "unknown type" ∷ [])
               } 
     ; t → typeError (strErr "unknown type" ∷ [])
     }

-- counter-reduce : (n : ℕ) → (goal : List (Arg Term)) → TC ⊤
-- counter-reduce zero    _          = typeError (strErr "time out" ∷ [])
-- counter-reduce (suc n) []         = returnTC tt
-- counter-reduce (suc n) (arg _ currentgoal ∷ goal) =
--   counter-reduce′ currentgoal >>=
--     λ { x → {!counter-reduce !} }

-- RAdd と RFrame を区別するようにしたもの
macro
  unify-reduce : (hole : Term) → TC ⊤
  unify-reduce hole = counter-reduce′ 10 hole


-- 3 + 5 ⟶ 8
test1 : Reduce* (Add term3 term5) (Val (Num 8))
test1 =
  begin
    Add term3 term5
  ⟶⟨ RAdd refl ⟩
    Val (Num 8)
  ∎

-- (3 + 5) + 4
test2 : Reduce* term35-4 term12
test2 =
  begin
    Add (Add term3 term5) term4
  ⟶⟨ RFrame (Add₁ term4) (RAdd refl) ⟩
    frame-plug (Add₁ term4) (Val (Num (3 + 5)))
  ⟶⟨ RAdd refl ⟩
    term12
  ∎

-- 4 + (3 + 5)
test3 : Reduce* term4-35 term12
test3 =
  begin
    Add (Val (Num 4)) (Add (Val (Num 3)) (Val (Num 5)))
   ⟶⟨ RFrame (Add₂ (Num 4)) (RAdd refl) ⟩
    frame-plug (Add₂ (Num 4)) (Val (Num (3 + 5)))
   ⟶⟨ RAdd refl ⟩
    term12
   ∎

-- (2 + 4) + (3 + 5) ⟶* 14
test4 : Reduce* (Add (Add (Val (Num 2)) (Val (Num 4))) (Add term3 term5)) (Val (Num 14))
test4 =
  begin
    Add (Add (Val (Num 2)) (Val (Num 4))) (Add term3 term5)
  ⟶⟨ RFrame (Add₁ (Add term3 term5)) (RAdd refl) ⟩
    frame-plug (Add₁ (Add term3 term5)) (Val (Num (2 + 4)))
  ⟶⟨ RFrame (Add₂ (Num 6)) (RAdd refl) ⟩
    frame-plug (Add₂ (Num 6)) (Val (Num (3 + 5)))
  ⟶⟨ RAdd refl ⟩
    Val (Num 14)
  ∎

-- 1 + (2 + 3) + 4
test5 : Reduce* (Add term1 (Add (Add term2 term3) term4)) (Val (Num 10))
test5 =
  begin
    Add term1 (Add (Add term2 term3) term4)
  ⟶⟨ RFrame (Add₂ (Num 1)) (RFrame (Add₁ term4) (RAdd refl)) ⟩
    frame-plug (Add₂ (Num 1)) (frame-plug (Add₁ term4) (Val (Num (2 + 3))))
  ⟶⟨ RFrame (Add₂ (Num 1)) (RAdd refl) ⟩
    frame-plug (Add₂ (Num 1)) (Val (Num (2 + 3 + 4)))
  ⟶⟨ RAdd refl ⟩
    Val (Num 10)
  ∎

