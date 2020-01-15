-- λ計算の証明を自動で出す

module lambda-macro where

open import Data.Nat
open import Function
open import Data.Unit using (⊤; tt)
open import Reflection using (newMeta)
open import Agda.Builtin.List using (List; _∷_; [])
open import Agda.Builtin.Bool using (true; false)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Agda.Builtin.Reflection renaming (bindTC to _>>=_)

infixr 5 _⇒_

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

-- Term : typ → Set₁
-- Term  τ = (var : typ → Set) → term[ var ] τ

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
         {e₁ e₂ : term[ var ] τ} →
         Reduce* e₁ e₂ → Reduce* e₁ e₂
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

{- 𝓋isible 𝓇elevant 𝒶rgument -}
vra : {A : Set} → A → Arg A
vra = arg (arg-info visible relevant)

{- 𝒽idden 𝓇elevant 𝒶rgument -}
hra : {A : Set} → A → Arg A
hra = arg (arg-info hidden relevant)

macro
  unify-refl : (hole : Term) → TC ⊤
  unify-refl hole =
    newMeta unknown >>= λ m →
    let V = def (quote begin_) (vra m ∷ []) in
    inferType V >>= λ I →
    quoteTC V >>= λ Q →
    checkType V I >>= λ C →
    unify hole (def (quote begin_) (vra m ∷ []))

counter-reduce : (n : ℕ) → (hole : Term) → TC ⊤
counter-reduce zero hole    = typeError (strErr "time out" ∷ [])
counter-reduce (suc n) hole = inferType hole >>=
  λ {(def (quote Reduce*) (_ ∷ _ ∷ arg _ x ∷ arg _ y ∷ [])) →
      newMeta unknown >>= λ m₁ →
      newMeta unknown >>= λ m₂ →
      newMeta unknown >>= λ m₃ →
      newMeta unknown >>= λ m₄ →
      newMeta unknown >>= λ m₅ →
      newMeta unknown >>= λ m₆ →

      -- let V = def (quote begin_) (vra m₁ ∷ []) in
      -- reduce V >>= λ v →
      -- unify hole v

      -- inferType (def (quote begin_) (vra m₁ ∷ [])) >>= λ h₁ →
      -- unify hole (def (quote begin_) (vra m₁ ∷ [])) >>= λ r →
      -- unify m₁   (def (quote _⟶⟨_⟩_)
      --            (vra m₂ ∷ vra m₃ ∷ vra m₄ ∷ [])) >>= λ r →
      -- quoteTC r >>= λ q →
      -- reduce q >>= λ r₁ →
      -- noConstraints (unquoteTC h₁)
            
      unify hole (def (quote begin_) (vra (def (quote _⟶⟨_⟩_)
                                           (vra m₁ ∷ vra m₂ ∷ vra m₃ ∷ []))
                                 ∷ [])) >>= λ _ →
      
     catchTC
     (unify m₃ (def (quote _∎) (vra m₄ ∷ [])) >>= λ _ →
      counter-reduce n m₂)
     (unify m₃ (def (quote _⟶⟨_⟩_) (vra m₄
                                     ∷ vra m₅
                                     ∷ vra m₆
                                     ∷ [])) >>= λ _ →
      counter-reduce n m₂ >>= λ _ →
      counter-reduce n m₃)
     ; (def (quote Reduce) (_ ∷ _ ∷ arg _ a ∷ _ ∷ []))
     → reduce a >>=
     λ { (con (quote App) (_ ∷ _ ∷ _ ∷ arg _ x ∷ arg _ y ∷ []))
         → reduce x >>=
         λ { (con (quote App) args) →
             newMeta unknown >>= λ m₁ →
             newMeta unknown >>= λ m₂ →
             unify hole  (con (quote RFrame)
                              (vra (con (quote App₁) (vra m₁ ∷ []))
                              ∷ vra m₂
                              ∷ [])) >>= λ _ →
              counter-reduce n m₂
            ; (con (quote Val) _)
              → reduce y >>=
              λ { (con (quote App) _) →
                  newMeta unknown >>= λ m₁ →
                  newMeta unknown >>= λ m₂ →
                  unify hole (con (quote RFrame)
                                  (vra (con (quote App₂) (vra m₁ ∷ []))
                                  ∷ vra m₂
                                  ∷ [])) >>= λ _ →
                  counter-reduce n m₂
                 ; (con (quote Val) _) →
                 newMeta unknown >>= λ m →
                 unify hole (con (quote RBeta) (vra m ∷ [])) >>= λ _ → 
                 counter-reduce n m
                 ; t → typeError (strErr "not a Value" ∷ [])
                 }
            ; t → typeError (strErr "neither App nor Val" ∷ [])
            }
        ; t → typeError (strErr "not an Application" ∷ [])
        }
     ; (def (quote Subst) (_ ∷ _ ∷ _ ∷ arg _ a ∷ _ ∷ _ ∷ []))
     → reduce a >>=
     λ { (lam _ (abs _ (con (quote Val) _)))
         → newMeta unknown >>= λ m →
          unify hole ((con (quote sVal) (vra m ∷ []))) >>= λ _ →
          counter-reduce n m
        ; (lam _ (abs _ (con (quote App) _)))
          → newMeta unknown >>= λ m₁
          → newMeta unknown >>= λ m₂ →
          unify hole ((con (quote sApp) (vra m₁ ∷ vra m₂ ∷ []))) >>= λ _ →
          counter-reduce n m₁ >>= λ _ →
          counter-reduce n m₂
        ; t →  typeError (strErr "not lambda" ∷ [])
        }
     ; (def (quote SubstVal) (_ ∷ _ ∷ _ ∷ arg _ a ∷ _ ∷ _ ∷ []))
     → reduce a >>=
     λ { (con (quote Var) _) →
         unify hole ((con (quote sVar=) []))
        ; (lam _ (abs _ (con (quote Var) _))) →
          catchTC
          (unify hole ((con (quote sVar=) [])))
          (unify hole ((con (quote sVar≠) [])))
        ; (lam _ (abs _ (con (quote Abst) (_ ∷ _ ∷ _ ∷ arg _ b ∷ []))))
            → newMeta unknown >>= λ m₁
            → newMeta unknown >>= λ m₂
            → newMeta unknown >>= λ m₃ →
            unify hole ((con (quote sFun) (vra m₁ ∷ [])))  >>= λ _ →
            
            inferType m₁ >>=    
            λ { (pi p (abs s x))
                → extendContext p (newMeta unknown) >>= λ b
                → unify m₁ (lam visible (abs s b)) >>= λ _
                → extendContext (vra m₂) 
                                (counter-reduce n b)
               ; t → typeError (termErr t ∷ [])
               }
            
        ; t → typeError (strErr "not lambda or Val" ∷ [])
        }
     ; t → typeError (strErr "not a reduction" ∷ [])
     }

-- 自動証明用のマクロ
macro
  runTC : (hole : Term) → TC ⊤
  runTC hole = counter-reduce 10 hole

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

termx′′ : {var : typ → Set} → term[ var ] ((Nat ⇒ Nat ⇒ Nat) ⇒ Nat ⇒ Nat ⇒ Nat)
termx′′ = Val (Abst (λ x → Val (Var x)))

-- λy.y
termy : {var : typ → Set} → term[ var ] (Nat ⇒ Nat)
termy = Val (Abst (λ y → Val (Var y)))

-- λfx.x
termfx : {var : typ → Set} → term[ var ] (Nat ⇒ Nat ⇒ Nat)
termfx = Val (Abst (λ f → Val (Abst (λ x → Val (Var x)))))

-- λfx.fx
termffx : {var : typ → Set} → term[ var ] ((Nat ⇒ Nat) ⇒ Nat ⇒ Nat)
termffx = Val (Abst (λ f → Val (Abst (λ x → App (Val (Var f)) (Val (Var x))))))

{----------------Proof1----------------}

-- @ (λx.x) 1 ⟶ 1
test1 : {var : typ → Set} →
  Reduce* {var} (App termx term1) term1
test1 = R*Trans (App (Val (Abst (λ x → Val (Var x)))) (Val (Num 1)))
          (Val (Num 1)) (Val (Num 1)) (RBeta (sVal sVar=))
          (R*Id (Val (Num 1)))
  -- begin
  --   App (Val (Abst (λ x → Val (Var x)))) (Val (Num 1))
  --   ⟶⟨ RBeta (sVal sVar=) ⟩
  --   Val (Num 1)
  -- ∎

{----------------Proof2----------------}

-- @ (@ (λx.x) (λy.y)) 3 ⟶ 3
test2 : {var : typ → Set} →
  Reduce* {var} (App (App (Val (Abst (λ z → Val (Var z)))) termy) term3) term3
-- test2 = {!runTC!}
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

-- (@ (@ (λfx.x) 3) 3) ⟶ 3
test4 : {var : typ → Set} →
  Reduce* {var} (App (App termfx term3) term3) term3
test4 =
  begin
    App (App termfx term3) term3
  ⟶⟨ RFrame (App₁ (Val (Num 3)))
       (RBeta (sVal (sFun (λ x → sVal sVar≠)))) ⟩
    frame-plug (App₁ term3) (Val (Abst (λ f → Val (Var f))))
  ⟶⟨ RBeta (sVal sVar=) ⟩
    Val (Num 3)
  ∎

{----------------Proof5----------------}

-- (@ (@ (@ (λx.x) (λfx.x)) 3) 3) ⟶ 3
test5 : {var : typ → Set} →
  Reduce* {var} (App (App (App termx′′ termfx) term3) term3) term3
test5 =
  begin
    App (App (App termx′′ termfx) term3) term3
  ⟶⟨ RFrame (App₁ term3)
             (RFrame (App₁ term3) (RBeta (sVal sVar=))) ⟩
    frame-plug (App₁ term3) (frame-plug (App₁ term3)
                                        (Val (Abst (λ f →
                                         Val (Abst (λ x → Val (Var x)))))))
  ⟶⟨ RFrame (App₁ term3) (RBeta (sVal (sFun (λ x → sVal sVar≠)))) ⟩
    frame-plug (App₁ (Val (Num 3))) (Val (Abst (λ z → Val (Var z))))
  ⟶⟨ RBeta (sVal sVar=) ⟩
    term3
  ∎

{----------------Proof6----------------}

-- @ (@ (λfx.fx) (λy.y)) 3 ⟶ 3
-- test6 : {var : typ → Set} →
--   Reduce* {var} (App (App termffx termy) term3) term3
-- test6 =
--   begin
--     App (App termffx termy) term3
--   ⟶⟨ RFrame (App₁ term3) (RBeta (sVal (sFun (λ f →
--                                       sApp (sVal sVar=)
--                                            (sVal sVar≠))))) ⟩
--     frame-plug (App₁ term3)
--       (Val
--        (Abst (λ x → App (Val (Abst (λ y → Val (Var y)))) (Val (Var x)))))
--   ⟶⟨ RBeta (sApp (sVal (sFun (λ x → sVal sVar≠))) (sVal sVar=)) ⟩
--     App (Val (Abst (λ z → Val (Var z)))) term3)
--   ⟶⟨ RBeta (sVal sVar=) ⟩
--     term3
--   ∎


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
-- ⟶ App₁ λfx.(@ (λfx.fx) f) ((λfx.fx)fx)

-- add one one ⟶ two
test7 : {var : typ → Set} →
  Reduce* {var}  (App (App add one) one) two
test7 =
  begin
    App (App add one) one
  ⟶⟨ RFrame (App₁ one) (RBeta (sVal (sFun (λ n → sVal
                                      (sFun λ f → sVal
                                      (sFun (λ x → {!!}))))))) ⟩
    {!!}
  ⟶⟨ {!!} ⟩
    {!!}
  ∎
