-- λ計算をPHOASの形式でかく

module lambda where

open import Data.Nat
open import Function
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

infixr 5 _⇒_

-- type
data typ : Set where
  Nat  : typ
  _⇒_ : typ → typ → typ

-- source term
mutual
  data value[_]_ (var : typ → Set) : typ → Set where
    Num  : (n : ℕ) → value[ var ] Nat
    Var  : {τ : typ} → var τ → value[ var ] τ
    Abst : {τ₁ τ₂ : typ} →
           (e₁ : var τ₂ → term[ var ] τ₁) → value[ var ] (τ₂ ⇒ τ₁)
           
  data term[_]_ (var : typ → Set) : typ → Set where
    Val  : {τ : typ} → value[ var ] τ → term[ var ] τ
    App  : {τ₁ τ₂ : typ} →
           (e₁ : term[ var ] (τ₂ ⇒ τ₁)) → (e₂ : term[ var ] τ₂) →
           term[ var ] τ₁

Value : typ → Set₁
Value τ = (var : typ → Set) → value[ var ] τ

Term : typ → Set₁
Term  τ = (var : typ → Set) → term[ var ] τ 

-- M [ v / x]
-- substitution relation
mutual
  data SubstVal {var : typ → Set} : {τ τ₁ : typ} →
    (var τ → value[ var ] τ₁) → value[ var ] τ → value[ var ] τ₁ → Set where
    -- (λx.x)[v] → v
    sVar= : {τ : typ} → {v : value[ var ] τ} →
            SubstVal (λ x → Var x) v v
    -- (λx.y)[v] → y
    sVar≠ : {τ τ₁ : typ} → {x : var τ₁} → {v : value[ var ] τ} → 
            SubstVal (λ y → Var x) v (Var x)
    -- (λx.n)[v] → n
    sNum  : {τ : typ} → {n : ℕ} → {v : value[ var ] τ} →
            SubstVal (λ y → Num n) v (Num n)
    -- (λy.λx.ey)[v] → λx.e'
    sFun  : {τ τ₁ τ₂ : typ} →
            {e  : var τ → var τ₂ → term[ var ] τ₁} →
            {v : value[ var ] τ} →
            {e′ : var τ₂ → term[ var ] τ₁} →
            ((x : var τ₂) →
            Subst (λ y → (e y) x) v (e′ x)) →
            SubstVal (λ y → (Abst (e y))) v (Abst e′)

  data Subst {var : typ → Set} : {τ τ₁ : typ} →
             (var τ → term[ var ] τ₁) →
             value[ var ] τ →
             term[ var ] τ₁ → Set where
    sVal : {τ τ₁ : typ} →
           {v₁ : var τ → value[ var ] τ₁} →
           {v : value[ var ] τ} →
           {v₁′ : value[ var ] τ₁} →
           SubstVal v₁ v v₁′ →
           Subst (λ y → Val (v₁ y)) v (Val v₁′)
    sApp : {τ τ₁ τ₂ : typ} →
           {e₁ : var τ → term[ var ] (τ₂ ⇒ τ₁)} →
           {e₂ : var τ → term[ var ] τ₂} →
           {v : value[ var ] τ} →
           {e₁′ : term[ var ] (τ₂ ⇒ τ₁)} →
           {e₂′ : term[ var ] τ₂} →
           Subst e₁ v e₁′ → Subst e₂ v e₂′ →
           Subst (λ y → App (e₁ y) (e₂ y)) v (App e₁′ e₂′)

-- E = [] | EM | VE 
-- frame
data frame[_,_] (var : typ → Set) : typ → typ → Set where
  App₁ : {τ₁ τ₂ : typ} →
         (e₂ : term[ var ] τ₂) →
         frame[ var , τ₂ ⇒ τ₁ ] τ₁
  App₂ : {τ₁ τ₂ : typ} →
         (v₁ : value[ var ] (τ₂ ⇒ τ₁)) →
         frame[ var , τ₂ ] τ₁

frame-plug : {var : typ → Set} → {τ₁ τ₂ : typ} →
             frame[ var , τ₂ ] τ₁ →
             term[ var ] τ₂ →
             term[ var ] τ₁
frame-plug (App₁ e₂) e₁ = App e₁ e₂
frame-plug (App₂ v₁) e₂ = App (Val v₁) e₂

--reduction relation (=preservation)
data Reduce {var : typ → Set} : {τ : typ} →
     term[ var ] τ → term[ var ] τ → Set where
  -- E[ (λx.e) v ] → E[ e′= e [v/x] ]
  RBeta : {τ₁ τ₂ : typ} →
          {e  : (x : var τ₂) → term[ var ] τ₁} →
          {v  : value[ var ] τ₂} →
          {e′ : term[ var ] τ₁} →
          Subst e v e′ →
          Reduce (App (Val (Abst e)) (Val v)) e′
  RFrame : {τ₁ τ₂ : typ} →
           {e : term[ var ] τ₁} →
           {e′ : term[ var ] τ₁} →
           (f : frame[ var , τ₁ ] τ₂) →
           Reduce e e′ →
           Reduce (frame-plug f e) (frame-plug f e′)

data Reduce* {var : typ → Set} : {τ₁ : typ} →
             term[ var ] τ₁ → term[ var ] τ₁ → Set where
  R*Id  : {τ₁ : typ} →
           (e : term[ var ] τ₁) →
           Reduce* e e
  R*Trans : {τ₁ : typ} →
           (e₁ : term[ var ] τ₁) →
           (e₂ : term[ var ] τ₁) →
           (e₃ : term[ var ] τ₁) →
           Reduce e₁ e₂ →
           Reduce* e₂ e₃ →
           Reduce* e₁ e₃

-- equational reasoning
-- see ≡-Reasoning in Relation.Binary.PropositionalEquality.agda

infix  3 _∎
infixr 2 _⟶⟨_⟩_ _⟶*⟨_⟩_ _≡⟨_⟩_
infix  1 begin_

begin_ : {var : typ → Set} → {τ : typ} →
         {e₁ e₂ : term[ var ] τ} → Reduce* e₁ e₂ → Reduce* e₁ e₂
begin_ red = red

_⟶⟨_⟩_ : {var : typ → Set} → {τ : typ} →
           (e₁ {e₂ e₃} : term[ var ] τ) → Reduce e₁ e₂ → Reduce* e₂ e₃ →
           Reduce* e₁ e₃
_⟶⟨_⟩_ e₁ {e₂} {e₃} e₁-red-e₂ e₂-red*-e₃ =
  R*Trans e₁ e₂ e₃ e₁-red-e₂ e₂-red*-e₃

_⟶*⟨_⟩_ : {var : typ → Set} → {τ : typ} →
            (e₁ {e₂ e₃} : term[ var ] τ) → Reduce* e₁ e₂ → Reduce* e₂ e₃ →
            Reduce* e₁ e₃
_⟶*⟨_⟩_ e₁ {.e₁} {e₃} (R*Id .e₁) e₁-red*-e₃ = e₁-red*-e₃
_⟶*⟨_⟩_ e₁ {.e₂} {e₃} (R*Trans .e₁ e₁′ e₂ e₁-red-e₁′ e₁′-red*-e₂) e₂-red*-e₃ =
  R*Trans e₁ e₁′ e₃ e₁-red-e₁′
          (e₁′ ⟶*⟨ e₁′-red*-e₂ ⟩ e₂-red*-e₃)

_≡⟨_⟩_ : {var : typ → Set} → {τ : typ} →
           (e₁ {e₂ e₃} : term[ var ] τ) → e₁ ≡ e₂ → Reduce* e₂ e₃ →
           Reduce* e₁ e₃
_≡⟨_⟩_ e₁ {e₂} {e₃} refl e₂-red*-e₃ = e₂-red*-e₃

_∎ : {var : typ → Set} → {τ : typ} →
     (e : term[ var ] τ) → Reduce* e e
_∎ e = R*Id e
 
{----------------Term Definition----------------}

-- 1
term1 : {var : typ → Set} → term[ var ] Nat
term1 = Val (Num 1)

-- 3
term3 : {var : typ → Set} → term[ var ] Nat
term3 = Val (Num 3)

-- λx.x
termx : {var : typ → Set} → term[ var ] (Nat ⇒ Nat)
termx = Val (Abst (λ x → Val (Var x)))

termx′ : {var : typ → Set} → term[ var ] ((Nat ⇒ Nat) ⇒ (Nat ⇒ Nat))
termx′ = Val (Abst (λ x → Val (Var x)))

-- λy.y
termy : {var : typ → Set} → term[ var ] (Nat ⇒ Nat)
termy = Val (Abst (λ y → Val (Var y)))

{----------------Proof1----------------}

-- @ (λx.x) 1 ⟶ 1
test1 : {var : typ → Set} →
  Reduce* {var} (App termx term1) term1
test1 =
  begin
    App (Val (Abst (λ x → Val (Var x)))) (Val (Num 1))
  ⟶⟨ RBeta (sVal sVar=) ⟩
    Val (Num 1)
  ∎

{----------------Proof2----------------}

-- @ (@ (λx.x) (λy.y)) 3 ⟶ 3
test2 : {var : typ → Set} →
  Reduce* {var} (App (App (Val (Abst (λ z → Val (Var z)))) termy) term3) term3
test2 =
  begin
    App
      (App (Val (Abst (λ z → Val (Var z))))
           (Val (Abst (λ z → Val (Var z)))))
      (Val (Num 3))
  ⟶⟨ RFrame (App₁ (Val (Num 3))) (RBeta (sVal sVar=)) ⟩
     frame-plug (App₁ (Val (Num 3))) (Val (Abst (λ z → Val (Var z))))
  ⟶⟨ RBeta (sVal sVar=) ⟩
    Val (Num 3)
  ∎

{----------------Proof3----------------}

-- @ (λx.x) (@ (λy.y) 3) ⟶ 3
test3 : {var : typ → Set} →
  Reduce* {var} (App termx (App termy term3)) term3
test3 =
  begin
    App (Val (Abst (λ z → Val (Var z))))
        (App (Val (Abst (λ z → Val (Var z))))
             (Val (Num 3)))
  ⟶⟨ RFrame (App₂ (Abst (λ z → Val (Var z)))) (RBeta (sVal sVar=)) ⟩
    frame-plug (App₂ (Abst (λ z → Val (Var z)))) (Val (Num 3))
  ⟶⟨ RBeta (sVal sVar=) ⟩
    Val (Num 3)
  ∎

{----------------Proof4----------------}

--    @ (@ (λx.x) (λy.y)) (@ (λx.x) 3)
-- ⟶ App₁ , RBeta
--    @ (λy.y) (@ (λx.x) 3)
-- ⟶ App₂ , RBeta
--    @ (λy.y) 3
-- ⟶ RBeta
--    3

-- @ (@ (λx.x) (λy.y)) (@ (λx.x) 3) ⟶ 3
test4 : {var : typ → Set} →
  Reduce* {var} (App (App termx′ termy) (App termx term3)) term3
test4 =
  begin
    App
      (App (Val (Abst (λ z → Val (Var z))))
           (Val (Abst (λ z → Val (Var z)))))
      (App (Val (Abst (λ z → Val (Var z))))
           (Val (Num 3)))
  ⟶⟨ RFrame (App₁ (App termx term3)) (RBeta (sVal sVar=)) ⟩
    frame-plug
      (App₁ (App termx term3)) (Val (Abst (λ z → Val (Var z))))
  ⟶⟨ RFrame (App₂ (Abst (λ z → Val (Var z)))) (RBeta (sVal sVar=)) ⟩
    frame-plug (App₂ (Abst (λ z → Val (Var z)))) (Val (Num 3))
  ⟶⟨ RBeta (sVal sVar=) ⟩
    Val (Num 3)
  ∎

{----------------Term Definition----------------}

-- FROM : TYPE THEORY ... Chapter2.Simply Typed Lambda Calculus

-- one : (α → α) → α → α
-- one := λfx.fx
one : {var : typ → Set} → term[ var ] ((Nat ⇒ Nat) ⇒ (Nat ⇒ Nat))
one = Val (Abst (λ f → Val (Abst
                   (λ x → App (Val (Var f)) (Val (Var x))))))

-- two : (α → α) → α → α
-- two := λfx.f(fx)
two : {var : typ → Set} → term[ var ] ((Nat ⇒ Nat) ⇒ (Nat ⇒ Nat))
two = Val (Abst (λ f → Val (Abst
                   (λ x → App (Val (Var f)) (App (Val (Var f)) (Val (Var x)))))))


-- add : ((α → α) → (α → α)) → ((α → α) → (α → α)) → (α → α) → α → α
-- add := λmnfx.mf(nfx)
add : {var : typ → Set} → term[ var ] (((Nat ⇒ Nat) ⇒ (Nat ⇒ Nat)) ⇒
                                      (((Nat ⇒ Nat) ⇒ (Nat ⇒ Nat)) ⇒
                                      ((Nat ⇒ Nat) ⇒
                                      (Nat ⇒ Nat))))
add = Val (Abst λ m → Val (Abst
                     (λ n → Val (Abst
                       (λ f → Val (Abst
                         (λ x → App (App (Val (Var m)) (Val (Var f)))
                                     (App (App (Val (Var n)) (Val (Var f)))
                                          (Val (Var x))))))))))


--     (@ (@ λmnfx.mf(nfx) λfx.fx) one)
-- ⟶ App₁ (@ λnfx.(λfx.fx)f(nfx) λfx.fx)
-- ⟶ App₁ λfx.(@ (λfx.fx) f) ((λfx.fx)fx) -- ここまでしかReduceできない...

-- ⟶ λfx.(λx.fx)((@ (λfx.fx) f) x)
-- ⟶ λfx.(λx.fx)(@ (λx.fx) x)
-- ⟶ λfx.(@ (λx.fx) (fx))
-- ⟶ λfx.f(fx)

-- add one one ⟶ two
test5 : {var : typ → Set} →
  Reduce* {var}  (App (App add one) one) two
test5 =
  begin
    App (App add one) one
  ⟶⟨ RFrame (App₁ one) (RBeta (sVal (sFun λ x → sVal
                                      (sFun λ x₁ → sVal
                                      (sFun (λ x₂ → sApp (sApp (sVal sVar=) (sVal sVar≠))
                                                         (sApp (sApp (sVal sVar≠) (sVal sVar≠))
                                                         (sVal sVar≠)))))))) ⟩
    frame-plug (App₁ one) ((Val (Abst (λ n → Val (Abst
                                      (λ f → Val (Abst
                                      (λ x → App (App one (Val (Var f)))
                                                 (App (App (Val (Var n)) (Val (Var f)))
                                                      (Val (Var x)))))))))))                                                         
  ⟶⟨ RBeta (sVal (sFun (λ x → sVal (sFun (λ f → sApp (sApp (sVal (sFun (λ x₁ → sVal (sFun
                                                                          (λ x₂ → sApp (sVal sVar≠)
                                                              (sVal sVar≠))))))
                                                        (sVal sVar≠))
                                                   (sApp (sApp (sVal sVar=) (sVal sVar≠))
                                                         (sVal sVar≠))))))) ⟩
    Val (Abst (λ f → Val (Abst (λ x → App (App one (Val (Var f)))
                                           (App (App one (Val (Var f)))
                                                (Val (Var x)))))))
  ≡⟨ {!!} ⟩
    two
  ∎

