module DSterm where

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
    Num   : ℕ → value[ var ] Nat cps[τ,τ]
    Var   : {τ₁ : typ} → var τ₁ → value[ var ] τ₁ cps[τ,τ]
    Fun   : (τ₁ τ₂ {τ₃ τ₄} : typ) →
            (var τ₂ → term[ var ] τ₁ cps[ τ₃ , τ₄ ]) →
            value[ var ] (τ₂ ⇒ τ₁ cps[ τ₃ , τ₄ ]) cps[τ,τ]
    Shift : {τ τ₁ τ₂ τ₃ τ₄ : typ} →
            value[ var ]
             (((τ₃ ⇒ τ₄ cps[ τ , τ ]) ⇒ τ₁ cps[ τ₁ , τ₂ ])
               ⇒ τ₃ cps[ τ₄ , τ₂ ])
               cps[τ,τ]


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
    -- Shift : (τ τ₁ τ₂ τ₃ τ₄ : typ) →
    --         (var (τ₃ ⇒ τ₄ cps[ τ , τ ]) →
    --         term[ var ] τ₁ cps[ τ₁ , τ₂ ]) →
    --         term[ var ] τ₃ cps[ τ₄ , τ₂ ]
    Let : {τ₁ τ₂ α β γ : typ} →
          term[ var ] τ₁ cps[ β , γ ] →                -- e1
          (var τ₁ → term[ var ] τ₂ cps[ α , β ]) →     -- λx. e2
          term[ var ] τ₂ cps[ α , γ ]

-- M[ v / x]
-- substitution relation
mutual
  data SubstVal {var : typ → Set} : {τ₁ τ₂ : typ} →
                (var τ₁ → value[ var ] τ₂ cps[τ,τ]) →
                value[ var ] τ₁ cps[τ,τ] →
                value[ var ] τ₂ cps[τ,τ] → Set where
　　 -- (λx.x)[v] → v                
    sVar=  : {τ₁ : typ} {v : value[ var ] τ₁ cps[τ,τ]} →
             SubstVal (λ x → Var x) v v
    -- (λ_.x)[v] → x
    sVar≠  : {τ₁ τ₂ : typ} {v : value[ var ] τ₂ cps[τ,τ]} {x : var τ₁} →
             SubstVal (λ _ → Var x) v (Var x)
    -- (λ_.n)[v] → n
    sNum   : {τ₁ : typ} {v : value[ var ] τ₁ cps[τ,τ]} {n : ℕ} →
             SubstVal (λ _ → Num n) v (Num n)
    -- (λ_.S)[v] → S
    sShift : {τ τ₁ τ₂ τ₃ τ₄ τ₅ : typ} {v : value[ var ] τ₅ cps[τ,τ]} →
             SubstVal (λ _ → Shift {τ = τ} {τ₁} {τ₂} {τ₃} {τ₄}) v Shift
    -- (λy.λx.ey)[v] → λx.e′
    sFun   : {τ τ₁ τ₂ τ₃ τ₄ : typ} →
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
    -- sShift : {τ τ₁ τ₂ τ₃ τ₄ τ₅ : typ} →
    --          {e₁ : var τ₅ →
    --                var (τ₃ ⇒ τ₄ cps[ τ , τ ]) →
    --                term[ var ] τ₁ cps[ τ₁ , τ₂ ]} →
    --          {v  : value[ var ]  τ₅ cps[τ,τ]} →
    --          {e₁′ : var (τ₃ ⇒ τ₄ cps[ τ , τ ]) →
    --                term[ var ] τ₁ cps[ τ₁ , τ₂ ]} →
    --          ((k : var (τ₃ ⇒ τ₄ cps[ τ , τ ])) →
    --                Subst (λ y → (e₁ y) k) v (e₁′ k)) →
    --          Subst (λ y → Shift τ τ₁ τ₂ τ₃ τ₄ (e₁ y))
    --                v
    --                (Shift τ τ₁ τ₂ τ₃ τ₄ e₁′)
    sReset : {τ τ₁ τ₂ τ₃ : typ} →
             {e₁ : var τ → term[ var ] τ₁ cps[ τ₁ , τ₂ ]} →
             {v : value[ var ] τ cps[τ,τ]} →
             {e₁′ : term[ var ] τ₁ cps[ τ₁ , τ₂ ]} →
             Subst e₁ v e₁′ →
             Subst {τ₃ = τ₃} (λ y → Reset τ₁ τ₂ τ₃ (e₁ y))
                   v
                   (Reset τ₁ τ₂ τ₃ e₁′)
    sLet   : {τ τ₁ τ₂ α β γ : typ} →
             {e₁ : var τ → term[ var ] τ₁ cps[ β , γ ]} →
             {e₂ : var τ → (var τ₁ → term[ var ] τ₂ cps[ α , β ])} →
             {v : value[ var ] τ cps[τ,τ]} →
             {e₁′ : term[ var ] τ₁ cps[ β , γ ]} →
             {e₂′ : var τ₁ → term[ var ] τ₂ cps[ α , β ]} →
             ((x : var τ₁) → Subst (λ y → (e₂ y) x) v (e₂′ x)) →
             Subst e₁ v e₁′ →
             Subst (λ y → Let (e₁ y) (e₂ y))
                   v
                   (Let e₁′ e₂′)

-- mutual
  DSubstV≠ : {var : typ → Set} {τ₁ τ₂ : typ} →
             {t : value[ var ] τ₁ cps[τ,τ]} →
             {v : value[ var ] τ₂ cps[τ,τ]} →
             SubstVal (λ y → t) v t
  DSubstV≠ {t = Num x} = sNum
  DSubstV≠ {t = Var x} = sVar≠
  DSubstV≠ {t = Fun τ₁ τ₃ e₁} = sFun (λ x → DSubst≠)
  DSubstV≠ {t = Shift} = sShift
  

  DSubst≠ : {var : typ → Set} {τ₁ τ₂ τ₃ τ₄ : typ} →
            {t : term[ var ] τ₁ cps[ τ₃ , τ₄ ]} →
            {v : value[ var ] τ₂ cps[τ,τ]} →
            Subst (λ y → t) v t      
  DSubst≠ {t = Val x} = sVal DSubstV≠
  DSubst≠ {t = App e₁ e₂} = sApp DSubst≠ DSubst≠
  DSubst≠ {t = Reset τ₁ τ₄ τ₃ e} = sReset DSubst≠
  DSubst≠ {t = Let e₁ e₂} = sLet (λ x → DSubst≠) DSubst≠
  -- DSubst≠ {t = Shift τ τ₁ τ₃ τ₄ τ₅ x} = sShift (λ k → DSubst≠)

-- E = [] | EM | VE
-- F = ([] @ e₂) | (v₁ @ []) | ⟨ [] ⟩ | let x = [] in e₂
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
  Let   : {τ₁ τ₂ α β γ : typ} →
          (e₂ : var τ₁ → term[ var ] τ₂ cps[ α , β ]) →
          frame[ var , τ₁ cps[ β , γ ]] τ₂ cps[ α , γ ]

frame-plug : {var : typ → Set}
             {τ₁ τ₂ τ₃ τ₄ τ₅ τ₆ : typ} →
             frame[ var , τ₂ cps[ τ₄ , τ₅ ]] τ₁ cps[ τ₃ , τ₆ ] →
             term[ var ] τ₂ cps[ τ₄ , τ₅ ] →
             term[ var ] τ₁ cps[ τ₃ , τ₆ ]
frame-plug (App₁ e₂) e₁ = App e₁ e₂
frame-plug (App₂ v₁) e₂ = App (Val v₁) e₂
frame-plug {τ₁ = τ₁} {τ₂} {τ₃} Reset e₁ = Reset τ₂ τ₁ τ₃ e₁
frame-plug (Let e₂) e₁ = Let e₁ e₂

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
  Let  : {τ₁ τ₂ α β γ : typ} →
         (e₂ : var τ₁ → term[ var ] τ₂ cps[ α , β ]) →
         pframe[ var , τ₁ cps[ β , γ ]] τ₂ cps[ α , γ ]

pframe-plug : {var : typ → Set}
             {τ₁ τ₂ τ₃ τ₄ τ₅ : typ} →
             pframe[ var , τ₂ cps[ τ₄ , τ₅ ]] τ₁ cps[ τ₃ , τ₅ ] →
             term[ var ] τ₂ cps[ τ₄ , τ₅ ] →
             term[ var ] τ₁ cps[ τ₃ , τ₅ ]
pframe-plug (App₁ e₂) e₁ = App e₁ e₂
pframe-plug (App₂ v₁) e₂ = App (Val v₁) e₂
pframe-plug (Let e₂)  e₁ = Let e₁ e₂

data same-pframe {var : typ → Set} {τ₁ τ₃ τ₅ τ₆ : typ} :
                 {τ τ₇ : typ} →
       pframe[ var , τ cps[ τ₅ , τ₆ ]] τ₁ cps[ τ₃ , τ₆ ] →
       pframe[ var , τ cps[ τ₅ , τ₇ ]] τ₁ cps[ τ₃ , τ₇ ] →
       Set where
  App₁ : {τ₂ τ₄ τ₆ : typ} →
         (e₂ : term[ var ] τ₂ cps[ τ₄ , τ₅ ]) →
         same-pframe (App₁ e₂)
                     (App₁ {τ₆ = τ₆} e₂)
  App₂ : {τ₂ τ₆ : typ} →
         (v₁ : value[ var ] (τ₂ ⇒ τ₁ cps[ τ₃ , τ₅ ]) cps[τ,τ]) →
         same-pframe (App₂ v₁)
                     (App₂ {τ₅ = τ₆} v₁)
  Let  : {τ α β : typ} →
         (e₂ : var τ → term[ var ] τ₁ cps[ τ₃ , τ₅ ]) →
         same-pframe (Let e₂)
                     (Let {γ = τ₆} e₂)

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

data same-pcontext {var : typ → Set} {τ₁ τ₂ τ₃ : typ} :
                   {τ₄ τ₆ τ₇ τ₈ : typ} →
       pcontext[ var , τ₁ cps[ τ₂ , τ₃ ]] τ₄ cps[ τ₇ , τ₃ ] →
       pcontext[ var , τ₁ cps[ τ₂ , τ₂ ]] τ₆ cps[ τ₇ , τ₈ ] →
       Set where
  Hole  : same-pcontext Hole Hole
  Frame : {τ₄ τ₅ τ₆ τ₇ : typ} →
          {f₁ : pframe[ var , τ₄ cps[ τ₅ , τ₃ ]] τ₆
                      cps[ τ₇ , τ₃ ]} →
          {f₂ : pframe[ var , τ₄ cps[ τ₅ , τ₂ ]] τ₆
                      cps[ τ₇ , τ₂ ]} →
          same-pframe f₁ f₂ →
          {p₁ : pcontext[ var , τ₁ cps[ τ₂ , τ₃ ]] τ₄
                        cps[ τ₅ , τ₃ ]} →
          {p₂ : pcontext[ var , τ₁ cps[ τ₂ , τ₂ ]] τ₄
                        cps[ τ₅ , τ₂ ]} →
          same-pcontext p₁ p₂ →
          same-pcontext (Frame f₁ p₁) (Frame f₂ p₂)

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
           Reduce e₁ e₂ →
           Reduce (frame-plug f e₁) (frame-plug f e₂)
  RLet   : {τ₁ τ₂ α β : typ} →
           {v₁ : value[ var ] τ₁ cps[τ,τ]} →
           {e₂ : var τ₁ → term[ var ] τ₂ cps[ α , β ]} →
           {e₂′ : term[ var ] τ₂ cps[ α , β ]} →
           Subst e₂ v₁ e₂′ →
           Reduce (Let (Val v₁) e₂) e₂′
  RReset : {τ₁ τ₂ : typ} →
           {v₁ : value[ var ] τ₁ cps[τ,τ]} →
           Reduce {τ₂ = τ₂} (Reset τ₁ τ₁ τ₂ (Val v₁)) (Val v₁)
  RShift : {τ τ₁ τ₂ τ₃ τ₄ τ₅ τ₆ : typ} →
           {v₂ : value[ var ] (τ₃ ⇒ τ₄ cps[ τ , τ ]) ⇒ τ₁ cps[ τ₁ , τ₂ ] cps[τ,τ]} →
           (p₁ : pcontext[ var , τ₃ cps[ τ₄ , τ₂ ]]
                           τ₅ cps[ τ₅ , τ₂ ]) →
           (p₂ : pcontext[ var , τ₃ cps[ τ₄ , τ₄ ]]
                           τ₅ cps[ τ₅ , τ₄ ]) →
           same-pcontext p₁ p₂ →
           Reduce (Reset τ₅ τ₂ τ₆
                         (pcontext-plug τ₃ p₁ (App (Val Shift) (Val v₂))))
                  (Reset τ₁ τ₂ τ₆
                         (App (Val v₂)
                              (Val (Fun τ₄ τ₃ (λ x →
                                     let e = pcontext-plug τ₃ p₂ (Val (Var x)) in
                                     Reset τ₅ τ₄ τ e)))))
   
  -- RShift : {τ₀ τ₁ τ₂ τ₃ τ₄ τ α  : typ} →
  --          (p₁ : pcontext[ var , τ₀ cps[ τ , τ₂ ]]
  --                          τ₄ cps[ τ₄ , τ₂ ]) →
  --          (p₂ : pcontext[ var , τ₀ cps[ τ , τ ]]
  --                          τ₄ cps[ τ₄ , τ ]) →
  --          same-pcontext p₁ p₂ → 
  --          (e₁ : var (τ₀ ⇒ τ cps[ α , α ]) →
  --                term[ var ] τ₁ cps[ τ₁ , τ₂ ]) →
  --          Reduce {τ₂ = τ₃}
  --                 (Reset τ₄ τ₂ τ₃
  --                   (pcontext-plug τ₀ p₁ (Shift α τ₁ τ₂ τ₀ τ e₁)))
  --                 (Reset τ₁ τ₂ τ₃
  --                   (App (Val (Fun τ₁ (τ₀ ⇒ τ cps[ α , α ]) e₁))
  --                        (Val (Fun τ τ₀ (λ x →
  --                               let e = pcontext-plug {τ₁ = τ₄} τ₀
  --                                                     p₂
  --                                                     (Val (Var x))
  --                               in Reset τ₄ τ α e)))))
