-- λ計算の規則にCPS変換の規則を加える
-- shift reset の規則も導入

module lambda-answer where

open import Data.Unit
open import Data.Empty
open import Data.Nat
open import Function
open import Relation.Binary.PropositionalEquality

-- type
data typ : Set where
  Nat          : typ
  Boolean      : typ
  _⇒_cps[_,_] : typ → typ → typ → typ → typ

-- source term
mutual
  data value[_]_cps[τ,τ] (var : typ → Set) : typ → Set where
    Num : ℕ → value[ var ] Nat cps[τ,τ]
    Var : {τ₁ : typ} → var τ₁ → value[ var ] τ₁ cps[τ,τ]
    Fun : (τ₁ τ₂ {τ₃ τ₄} : typ) →
          (var τ₂ → term[ var ] τ₁ cps[ τ₃ , τ₄ ]) →
          value[ var ] (τ₂ ⇒ τ₁ cps[ τ₃ , τ₄ ]) cps[τ,τ]

  data term[_]_cps[_,_] (var : typ → Set) : typ → typ → typ → Set where
    Val   : {τ₁ τ₂ : typ} →
            value[ var ] τ₁ cps[τ,τ] →
            term[ var ] τ₁ cps[ τ₂ , τ₂ ]
    App   : {τ₁ τ₂ τ₃ τ₄ τ₅ τ₆ : typ} →
            term[ var ] (τ₂ ⇒ τ₁ cps[ τ₃ , τ₄ ]) cps[ τ₅ , τ₆ ] →
            term[ var ] τ₂ cps[ τ₄ , τ₅ ] →
            term[ var ] τ₁ cps[ τ₃ , τ₆ ]
    Reset : (τ₁ τ₂ τ₃ : typ) →
            term[ var ] τ₁ cps[ τ₁ , τ₂ ] →
            term[ var ] τ₂ cps[ τ₃ , τ₃ ]
    Shift : (τ τ₁ τ₂ τ₃ τ₄ : typ) →
            (var (τ₃ ⇒ τ₄ cps[ τ , τ ]) →
            term[ var ] τ₁ cps[ τ₁ , τ₂ ]) →
            term[ var ] τ₃ cps[ τ₄ , τ₂ ]

-- M[ v / x]
-- substitution relation
mutual
  data SubstVal {var : typ → Set} : {τ₁ τ₂ : typ} →
                (var τ₁ → value[ var ] τ₂ cps[τ,τ]) →
                value[ var ] τ₁ cps[τ,τ] →
                value[ var ] τ₂ cps[τ,τ] → Set where
　　 -- (λx.x)[v] → v                
    sVar= : {τ₁ : typ} {v : value[ var ] τ₁ cps[τ,τ]} →
            SubstVal (λ x → Var x) v v
    -- (λ_.x)[v] → x
    sVar≠ : {τ₁ τ₂ : typ} {v : value[ var ] τ₂ cps[τ,τ]} {x : var τ₁} →
            SubstVal (λ _ → Var x) v (Var x)
    -- (λ_.n)[v] → n
    sNum  : {τ₁ : typ} {v : value[ var ] τ₁ cps[τ,τ]} {n : ℕ} →
            SubstVal (λ _ → Num n) v (Num n)
    -- (λy.λx.ey)[v] → λx.e′
    sFun  : {τ τ₁ τ₂ τ₃ τ₄ : typ} →
            {e₁ : var τ₁ → var τ → term[ var ] τ₂ cps[ τ₃ , τ₄ ]} →
            {v : value[ var ] τ₁ cps[τ,τ]} →
            {e₁′ : var τ → term[ var ] τ₂ cps[ τ₃ , τ₄ ]} →
            ((x : var τ) → Subst (λ y → (e₁ y) x) v (e₁′ x)) →
            SubstVal (λ y → Fun τ₂ τ (e₁ y))
                     v
                     (Fun τ₂ τ e₁′)

  data Subst {var : typ → Set} : {τ₁ τ₂ τ₃ τ₄ : typ} →
             (var τ₁ → term[ var ] τ₂ cps[ τ₃ , τ₄ ]) →
             value[ var ] τ₁ cps[τ,τ] →
             term[ var ] τ₂ cps[ τ₃ , τ₄ ] → Set where
    sVal  : {τ τ₁ τ₂ : typ} →
            {v₁ : var τ → value[ var ] τ₁ cps[τ,τ]} →
            {v : value[ var ] τ cps[τ,τ]} →
            {v₁′ : value[ var ] τ₁ cps[τ,τ]} →
            SubstVal v₁ v v₁′ →
            Subst {τ₃ = τ₂} (λ y → Val (v₁ y)) v (Val v₁′)
    sApp  : {τ τ₁ τ₂ τ₃ τ₄ τ₅ τ₆ : typ} →
            {e₁ : var τ → term[ var ] (τ₂ ⇒ τ₁ cps[ τ₃ , τ₄ ])
                                      cps[ τ₅ , τ₆ ]}
            {e₂ : var τ → term[ var ] τ₂ cps[ τ₄ , τ₅ ]}
            {v : value[ var ] τ cps[τ,τ]}
            {e₁′ : term[ var ] (τ₂ ⇒ τ₁ cps[ τ₃ , τ₄ ])
                               cps[ τ₅ , τ₆ ]}
            {e₂′ : term[ var ] τ₂ cps[ τ₄ , τ₅ ]} →
            Subst e₁ v e₁′ → Subst e₂ v e₂′ →
            Subst (λ y → App (e₁ y) (e₂ y))
                  v
                  (App e₁′ e₂′)
    sShift : {τ τ₁ τ₂ τ₃ τ₄ τ₅ : typ} →
             {e₁ : var τ₅ →
                   var (τ₃ ⇒ τ₄ cps[ τ , τ ]) →
                   term[ var ] τ₁ cps[ τ₁ , τ₂ ]} →
             {v  : value[ var ]  τ₅ cps[τ,τ]} →
             {e₁′ : var (τ₃ ⇒ τ₄ cps[ τ , τ ]) →
                   term[ var ] τ₁ cps[ τ₁ , τ₂ ]} →
             ((k : var (τ₃ ⇒ τ₄ cps[ τ , τ ])) →
                   Subst (λ y → (e₁ y) k) v (e₁′ k)) →
             Subst (λ y → Shift τ τ₁ τ₂ τ₃ τ₄ (e₁ y))
                   v
                   (Shift τ τ₁ τ₂ τ₃ τ₄ e₁′)
    sReset : {τ τ₁ τ₂ τ₃ : typ} →
             {e₁ : var τ → term[ var ] τ₁ cps[ τ₁ , τ₂ ]} →
             {v : value[ var ] τ cps[τ,τ]} →
             {e₁′ : term[ var ] τ₁ cps[ τ₁ , τ₂ ]} →
             Subst e₁ v e₁′ →
             Subst {τ₃ = τ₃} (λ y → Reset τ₁ τ₂ τ₃ (e₁ y))
                   v
                   (Reset τ₁ τ₂ τ₃ e₁′)

-- E = [] | EM | VE
-- F = ([] @ e₂) | (v₁ @ []) | ⟨ [] ⟩
-- frame
data frame[_,_cps[_,_]]_cps[_,_] (var : typ → Set)
     : typ → typ → typ → typ → typ → typ → Set where
  -- [ (τ₂→τ₁@cps[τ₃,τ₄]) @ cps[τ₅,τ₆] ]
  App₁  : {τ₁ τ₂ τ₃ τ₄ τ₅ τ₆ : typ} →
          (e₂ : term[ var ] τ₂ cps[ τ₄ , τ₅ ]) →
          frame[ var , (τ₂ ⇒ τ₁ cps[ τ₃ , τ₄ ]) cps[ τ₅ , τ₆ ]]
                 τ₁ cps[ τ₃ , τ₆ ]
  App₂  : {τ₁ τ₂ τ₃ τ₄ τ₅ : typ} →
          (v₁ : value[ var ] (τ₂ ⇒ τ₁ cps[ τ₃ , τ₄ ]) cps[τ,τ]) →
          frame[ var , τ₂ cps[ τ₄ , τ₅ ]] τ₁ cps[ τ₃ , τ₅ ]
  Reset : {τ₁ τ₂ τ₃ : typ} →
          frame[ var , τ₁ cps[ τ₁ , τ₂ ]] τ₂ cps[ τ₃ , τ₃ ]

frame-plug : {var : typ → Set}
             {τ₁ τ₂ τ₃ τ₄ τ₅ τ₆ : typ} →
             frame[ var , τ₂ cps[ τ₄ , τ₅ ]] τ₁ cps[ τ₃ , τ₆ ] →
             term[ var ] τ₂ cps[ τ₄ , τ₅ ] →
             term[ var ] τ₁ cps[ τ₃ , τ₆ ]
frame-plug (App₁ e₂) e₁ = App e₁ e₂
frame-plug (App₂ v₁) e₂ = App (Val v₁) e₂
frame-plug {τ₁ = τ₁} {τ₂} {τ₃} Reset e₁ = Reset τ₂ τ₁ τ₃ e₁

-- pure frame
data pframe[_,_cps[_,_]]_cps[_,_] (var : typ → Set)
     : typ → typ → typ → typ → typ → typ → Set where
  App₁ : {τ₁ τ₂ τ₃ τ₄ τ₅ τ₆ : typ} →
         (e₂ : term[ var ] τ₂ cps[ τ₄ , τ₅ ]) →
         pframe[ var , (τ₂ ⇒ τ₁ cps[ τ₃ , τ₄ ]) cps[ τ₅ , τ₆ ]]
               τ₁ cps[ τ₃ , τ₆ ]
  App₂ : {τ₁ τ₂ τ₃ τ₄ τ₅ : typ} →
         (v₁ : value[ var ] (τ₂ ⇒ τ₁ cps[ τ₃ , τ₄ ]) cps[τ,τ]) →
         pframe[ var , τ₂ cps[ τ₄ , τ₅ ]] τ₁ cps[ τ₃ , τ₅ ]

pframe-plug : {var : typ → Set}
             {τ₁ τ₂ τ₃ τ₄ τ₅ : typ} →
             pframe[ var , τ₂ cps[ τ₄ , τ₅ ]] τ₁ cps[ τ₃ , τ₅ ] →
             term[ var ] τ₂ cps[ τ₄ , τ₅ ] →
             term[ var ] τ₁ cps[ τ₃ , τ₅ ]
pframe-plug (App₁ e₂) e₁ = App e₁ e₂
pframe-plug (App₂ v₁) e₂ = App (Val v₁) e₂

-- wf-pframe : {var : typ → Set}
--             {τ₁ τ₂ τ₃ τ₄ τ₅ : typ} {a a₂ : ann} →
--             pframe[ var , τ₂ cps[ τ₄ , τ₅ , a₂ ]] τ₁ cps[ τ₃ , τ₅ , a ] →
--             τ₃ ≠ τ₅ ⇒ a =i
-- wf-pframe {a = P} (App₁ P≤ₐP P≤ₐP P≤ₐP refl refl refl e₂) = refl
-- wf-pframe {a = I} (App₁ leq₁ leq₂ leq₃ c₁ c₂ c₃ e₂) = tt
-- wf-pframe {a = P} (App₂ P≤ₐP P≤ₐP refl refl v₁) = refl
-- wf-pframe {a = I} (App₂ leq₁ leq₂ c₁ c₂ v₁) = tt

-- data same-pframe {var : typ → Set} {τ₁ τ₃ τ₅ τ₆ : typ} :
--                  {τ τ₇ : typ} →
--        pframe[ var , τ cps[ τ₅ , τ₆ , I ]] τ₁ cps[ τ₃ , τ₆ , I ] →
--        pframe[ var , τ cps[ τ₅ , τ₇ , a₁ ]] τ₁ cps[ τ₃ , τ₇ , a ] →
--        Set where
--   App₁ : {τ₂ τ₄ : typ} → {a₂ a₃ : ann} →
--          (a₁≤ₐa : a₁ ≤ₐ a) → (a₂≤ₐa : a₂ ≤ₐ a) → (a₃≤ₐa : a₃ ≤ₐ a) →
--          (c₁ : τ₅ ≠ τ₆ ⇒ a₁ =i) → (c₂ : τ₄ ≠ τ₅ ⇒ a₂ =i) →
--          (c₃ : τ₃ ≠ τ₄ ⇒ a₃ =i) →
--          (e₂ : term[ var ] τ₂ cps[ τ₄ , τ₅ , a₂ ]) →
--          same-pframe (App₁ I≤ₐI a≤ₐI a≤ₐI tt c₂ c₃ e₂)
--                      (App₁ a₁≤ₐa a₂≤ₐa a₃≤ₐa c₁ c₂ c₃ e₂)
--   App₂ : {τ τ₂ τ₇ : typ} {a₃ : ann} →
--          (a₁≤ₐa : a₁ ≤ₐ a) → (a₃≤ₐa : a₃ ≤ₐ a) →
--          (c₁ : τ₅ ≠ τ₇ ⇒ a₁ =i) → (c₃ : τ₃ ≠ τ₅ ⇒ a₃ =i) →
--          (v₁ : value[ var ] (τ₂ ⇒ τ₁ cps[ τ₃ , τ₅ , a₃ ]) cps[τ,τ,P]) →
--          same-pframe (App₂ I≤ₐI a≤ₐI tt c₃ v₁)
--                      (App₂ a₁≤ₐa a₃≤ₐa c₁ c₃ v₁)

-- pure context : for RShift
data pcontext[_,_cps[_,_]]_cps[_,_] (var : typ → Set)
     : typ → typ → typ → typ → typ → typ → Set where
  Hole  : {τ₁ τ₂ τ₃ : typ} →
          pcontext[ var , τ₁ cps[ τ₂ , τ₃ ]] τ₁ cps[ τ₂ , τ₃ ]
  Frame : {τ₁ τ₂ τ₃ τ₄ τ₅ τ₆ τ₇ : typ} →
          (f : pframe[ var , τ₄ cps[ τ₅ , τ₃ ]] τ₆
                     cps[ τ₇ , τ₃ ]) →
          (e : pcontext[ var , τ₁ cps[ τ₂ , τ₃ ]] τ₄
                       cps[ τ₅ , τ₃ ]) →
          pcontext[ var , τ₁ cps[ τ₂ , τ₃ ]] τ₆ cps[ τ₇ , τ₃ ]

pcontext-plug : {var : typ → Set}
                ({τ₁} τ₂ {τ₃ τ₄ τ₅} : typ) →
                pcontext[ var , τ₂ cps[ τ₄ , τ₅ ]] τ₁
                        cps[ τ₃ , τ₅ ] →
                term[ var ] τ₂ cps[ τ₄ , τ₅ ] →
                term[ var ] τ₁ cps[ τ₃ , τ₅ ]
pcontext-plug τ₂ Hole        e₁ = e₁
pcontext-plug τ₂ (Frame f p) e₁ = pframe-plug f (pcontext-plug τ₂ p e₁)                

-- wf-pcontext : {var : typ → Set}
--               {τ₁ τ₂ τ₃ τ₄ τ₅ : typ} {a a₂ : ann} →
--               pcontext[ var , τ₂ cps[ τ₄ , τ₅ , a₂ ]] τ₁
--                       cps[ τ₃ , τ₅ , a ] →
--               τ₃ ≠ τ₅ ⇒ a =i
-- wf-pcontext (Hole c) = c
-- wf-pcontext (Frame f p) = wf-pframe f

-- data same-pcontext {var : typ → Set} {τ₁ τ₂ τ₃ : typ} :
--                    {τ₄ τ₆ τ₇ τ₈ : typ} {a : ann} →
--        pcontext[ var , τ₁ cps[ τ₂ , τ₃ , I ]] τ₄ cps[ τ₇ , τ₃ , I ] →
--        pcontext[ var , τ₁ cps[ τ₂ , τ₂ , P ]] τ₆ cps[ τ₇ , τ₈ , a ] →
--        Set where
--   Hole  : same-pcontext (Hole tt) (Hole refl)
--   Frame : {τ₄ τ₅ τ₆ τ₇ : typ} → {a₂ a₃ : ann} →
--           {f₁ : pframe[ var , τ₄ cps[ τ₅ , τ₃ , I ]] τ₆
--                       cps[ τ₇ , τ₃ , I ]} →
--           {f₂ : pframe[ var , τ₄ cps[ τ₅ , τ₂ , a₂ ]] τ₆
--                       cps[ τ₇ , τ₂ , a₃ ]} →
--           same-pframe f₁ f₂ →
--           {p₁ : pcontext[ var , τ₁ cps[ τ₂ , τ₃ , I ]] τ₄
--                         cps[ τ₅ , τ₃ , I ]} →
--           {p₂ : pcontext[ var , τ₁ cps[ τ₂ , τ₂ , P ]] τ₄
--                         cps[ τ₅ , τ₂ , a₂ ]} →
--           same-pcontext p₁ p₂ →
--           same-pcontext (Frame f₁ p₁) (Frame f₂ p₂)

-- reduction rules
data Reduce {var : typ → Set} :
            {τ₁ τ₂ τ₃ : typ} →
            term[ var ] τ₁ cps[ τ₂ , τ₃ ] →
            term[ var ] τ₁ cps[ τ₂ , τ₃ ] → Set where
  RBeta  : {τ τ₁ τ₂ τ₃ : typ} →
           {e₁ : var τ → term[ var ] τ₁ cps[ τ₂ , τ₃ ]} →
           {v₂ : value[ var ] τ cps[τ,τ]} →
           {e₁′ : term[ var ] τ₁ cps[ τ₂ , τ₃ ]} →
           Subst e₁ v₂ e₁′ →
           Reduce (App (Val (Fun τ₁ τ e₁)) (Val v₂))
                  e₁′
  RFrame : {τ₁ τ₂ τ₃ τ₄ τ₅ τ₆ : typ} →
           {e₁ : term[ var ] τ₁ cps[ τ₂ , τ₃ ]} →
           {e₂ : term[ var ] τ₁ cps[ τ₂ , τ₃ ]} →
           (f : frame[ var , τ₁ cps[ τ₂ , τ₃ ]]
                     τ₄ cps[ τ₅ , τ₆ ]) →
           -- {f : frame[ var , τ₁ cps[ τ₂ , τ₃ ]]
           --           τ₄ cps[ τ₅ , τ₆ ]} →
           Reduce e₁ e₂ →
           Reduce (frame-plug f e₁) (frame-plug f e₂)
  RReset : {τ₁ τ₂ : typ} →
           {v₁ : value[ var ] τ₁ cps[τ,τ]} →
           Reduce {τ₂ = τ₂} (Reset τ₁ τ₁ τ₂ (Val v₁)) (Val v₁)
  RShift : {τ₀ τ₁ τ₂ τ₃ τ₄ τ α  : typ} →
           (p₁ : pcontext[ var , τ₀ cps[ τ , τ₂ ]]
                           τ₄ cps[ τ₄ , τ₂ ]) →
           (p₂ : pcontext[ var , τ₀ cps[ τ , τ ]]
                           τ₄ cps[ τ₄ , τ ]) →
           (e₁ : var (τ₀ ⇒ τ cps[ α , α ]) →
                 term[ var ] τ₁ cps[ τ₁ , τ₂ ]) →
           Reduce {τ₂ = τ₃}
                  (Reset τ₄ τ₂ τ₃
                    (pcontext-plug τ₀ p₁ (Shift α τ₁ τ₂ τ₀ τ e₁)))
                  (Reset τ₁ τ₂ τ₃
                    (App (Val (Fun τ₁ (τ₀ ⇒ τ cps[ α , α ]) e₁))
                         (Val (Fun τ τ₀ (λ x →
                                let e = pcontext-plug {τ₁ = τ₄} τ₀
                                                      p₂
                                                      (Val (Var x))
                                in Reset τ₄ τ α e)))))

data Reduce* {var : typ → Set} :
             {τ₁ τ₂ τ₃ : typ} →
             term[ var ] τ₁ cps[ τ₂ , τ₃ ] →
             term[ var ] τ₁ cps[ τ₂ , τ₃ ] → Set where
  R*Id    : {τ₁ τ₂ τ₃ : typ} →
            (e : term[ var ] τ₁ cps[ τ₂ , τ₃ ]) →
            Reduce* e e
  R*Trans : {τ₁ τ₂ τ₃ : typ} →
            (e₁ : term[ var ] τ₁ cps[ τ₂ , τ₃ ]) →
            (e₂ : term[ var ] τ₁ cps[ τ₂ , τ₃ ]) →
            (e₃ : term[ var ] τ₁ cps[ τ₂ , τ₃ ]) →
            Reduce e₁ e₂ →
            Reduce* e₂ e₃ →
            Reduce* e₁ e₃

-- equational reasoning
-- see ≡-Reasoning in Relation.Binary.PropositionalEquality.agda

infix  3 _∎
infixr 2 _⟶⟨_⟩_ _⟶*⟨_⟩_ _≡⟨_⟩_
infix  1 begin_

begin_ : {var : typ → Set} → {τ₁ τ₂ : typ} →
         {e₁ e₂ : term[ var ] τ₁ cps[ τ₂ , τ₂ ]} →
         Reduce* e₁ e₂ → Reduce* e₁ e₂
begin_ red = red

_⟶⟨_⟩_ : {var : typ → Set} → {τ₁ τ₂ : typ} →
           (e₁ {e₂ e₃} : term[ var ] τ₁ cps[ τ₂ , τ₂ ]) →
           Reduce e₁ e₂ → Reduce* e₂ e₃ →
           Reduce* e₁ e₃
_⟶⟨_⟩_ e₁ {e₂} {e₃} e₁-red-e₂ e₂-red*-e₃ =
  R*Trans e₁ e₂ e₃ e₁-red-e₂ e₂-red*-e₃

_⟶*⟨_⟩_ : {var : typ → Set} → {τ₁ τ₂ : typ} →
            (e₁ {e₂ e₃} : term[ var ] τ₁ cps[ τ₂ , τ₂ ]) →
            Reduce* e₁ e₂ → Reduce* e₂ e₃ →
            Reduce* e₁ e₃
_⟶*⟨_⟩_ e₁ {.e₁} {e₃} (R*Id .e₁) e₁-red*-e₃ = e₁-red*-e₃
_⟶*⟨_⟩_ e₁ {.e₂} {e₃} (R*Trans .e₁ e₁′ e₂ e₁-red-e₁′ e₁′-red*-e₂) e₂-red*-e₃ =
  R*Trans e₁ e₁′ e₃ e₁-red-e₁′
          (e₁′ ⟶*⟨ e₁′-red*-e₂ ⟩ e₂-red*-e₃)

_≡⟨_⟩_ : {var : typ → Set} → {τ₁ τ₂ : typ} →
           (e₁ {e₂ e₃} : term[ var ] τ₁ cps[ τ₂ , τ₂ ]) →
           e₁ ≡ e₂ → Reduce* e₂ e₃ →
           Reduce* e₁ e₃
_≡⟨_⟩_ e₁ {e₂} {e₃} refl e₂-red*-e₃ = e₂-red*-e₃

_∎ : {var : typ → Set} → {τ₁ τ₂ : typ} →
     (e : term[ var ] τ₁ cps[ τ₂ , τ₂ ]) → Reduce* e e
_∎ e = R*Id e

{----------------Term Definition----------------}

-- 1
term1 : {var : typ → Set} → {τ : typ} →
        term[ var ] Nat cps[ τ , τ ]
term1 = Val (Num 1)

-- ⟨ (λx.x) @ (Sk.k) ⟩ @ 1
termsk : {var : typ → Set} → term[ var ] Nat cps[ Nat , Nat ]
termsk = App (Reset Nat (Nat ⇒ Nat cps[ Nat , Nat ]) Nat
                   (App (Val (Fun Nat Nat (λ x → Val (Var x))))
                        (Shift Nat (Nat ⇒ Nat cps[ _ , _ ]) (Nat ⇒ Nat cps[ _ , _ ]) Nat Nat
                               (λ k → Val (Var k)))))
            term1

--    ⟨ (λx.x) @ (Sk.k) ⟩ @ 1
-- ⟶ ⟨ (λx.x) @ (λk.⟨ k ⟩) ⟩ @ 1
-- ⟶ ⟨ λk.⟨ k ⟩ ⟩ @ 1
-- ⟶ ⟨ 1 ⟩
-- ⟶ 1
test1 : {var : typ → Set} →
        Reduce* {var} termsk term1
test1 =
  begin
    termsk
  ⟶⟨ RFrame (App₁ (Val (Num 1)))
             (RShift (Frame (App₂ (Fun Nat Nat (λ k → Val (Var k)))) Hole)
                     Hole
                     λ x → Val (Var x)) ⟩
    -- frame-plug (App₁ (Val (Num 1)))
    --            (Reset (Nat ⇒ Nat cps[ Nat , Nat ]) (Nat ⇒ Nat cps[ Nat , Nat ]) Nat
    --                   (App (Val (Fun (Nat ⇒ Nat cps[ Nat , Nat ]) (Nat ⇒ Nat cps[ Nat , Nat ])
    --                             (λ x → Val (Var x))))
    --                        (Val (Fun Nat Nat
    --                                  (λ k → Reset Nat Nat Nat
    --                                               (pcontext-plug Nat Hole (Val (Var k))))))))
      App
        (Reset (Nat ⇒ Nat cps[ Nat , Nat ]) (Nat ⇒ Nat cps[ Nat , Nat ]) Nat
               (App (Val (Fun (Nat ⇒ Nat cps[ Nat , Nat ]) (Nat ⇒ Nat cps[ Nat , Nat ])
                              (λ x → Val (Var x))))
                    (Val (Fun Nat Nat (λ k → Reset Nat Nat Nat (Val (Var k)))))))
        (Val (Num 1))
  ⟶⟨ RFrame (App₁ (Val (Num 1)))
             (RFrame Reset (RBeta (sVal sVar=))) ⟩
    frame-plug (App₁ (Val (Num 1)))
               (frame-plug Reset (Val (Fun Nat Nat
                                           (λ k → Reset Nat Nat Nat
                                                        (pcontext-plug Nat Hole (Val (Var k)))))))
  ⟶⟨ RFrame (App₁ (Val (Num 1))) RReset ⟩
    -- frame-plug (App₁ (Val (Num 1)))
    --            (Val (Fun Nat Nat
    --                      (λ k → Reset Nat Nat Nat
    --                                   (pcontext-plug Nat Hole (Val (Var k))))))
      App (Val (Fun Nat Nat (λ k → Reset Nat Nat Nat (Val (Var k)))))
          (Val (Num 1))
  ⟶⟨ RBeta (sReset (sVal sVar=)) ⟩
    Reset Nat Nat Nat (Val (Num 1))
  ⟶⟨ RReset ⟩
    term1
  ∎
