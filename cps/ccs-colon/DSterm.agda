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

  data nonvalue[_]_cps[_,_] (var : typ → Set) : typ → typ → typ → Set where
    App   : {τ₁ τ₂ τ₃ τ₄ τ₅ τ₆ : typ} →
            term[ var ] (τ₂ ⇒ τ₁ cps[ τ₃ , τ₄ ]) cps[ τ₅ , τ₆ ] →
            term[ var ] τ₂ cps[ τ₄ , τ₅ ] →
            nonvalue[ var ] τ₁ cps[ τ₃ , τ₆ ]
    Reset : (τ₁ τ₂ τ₃ : typ) →
            term[ var ] τ₁ cps[ τ₁ , τ₂ ] →
            nonvalue[ var ] τ₂ cps[ τ₃ , τ₃ ]
    Let   : {τ₁ τ₂ α β γ : typ} →
            term[ var ] τ₁ cps[ β , γ ] →                -- e1
            (var τ₁ → term[ var ] τ₂ cps[ α , β ]) →    -- λx. e2
            nonvalue[ var ] τ₂ cps[ α , γ ]

  data term[_]_cps[_,_] (var : typ → Set) : typ → typ → typ → Set where
    Val    : {τ₁ τ₂ : typ} →
             value[ var ] τ₁ cps[τ,τ] →
             term[ var ] τ₁ cps[ τ₂ , τ₂ ]
    NonVal : {τ₁ τ₂ τ₃ : typ} →
             nonvalue[ var ] τ₁ cps[ τ₂ , τ₃ ] →
             term[ var ] τ₁ cps[ τ₂ , τ₃ ]

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
    -- -- (λ_.n)[v] → n
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
            Subst (λ y → NonVal (App (e₁ y) (e₂ y)))
                  v
                  (NonVal (App e₁′ e₂′))
    sReset : {τ τ₁ τ₂ τ₃ : typ} →
             {e₁ : var τ → term[ var ] τ₁ cps[ τ₁ , τ₂ ]} →
             {v : value[ var ] τ cps[τ,τ]} →
             {e₁′ : term[ var ] τ₁ cps[ τ₁ , τ₂ ]} →
             Subst e₁ v e₁′ →
             Subst {τ₃ = τ₃} (λ y → NonVal (Reset τ₁ τ₂ τ₃ (e₁ y)))
                   v
                   (NonVal (Reset τ₁ τ₂ τ₃ e₁′))
    sLet   : {τ τ₁ τ₂ α β γ : typ} →
             {e₁ : var τ → term[ var ] τ₁ cps[ β , γ ]} →
             {e₂ : var τ → (var τ₁ → term[ var ] τ₂ cps[ α , β ])} →
             {v : value[ var ] τ cps[τ,τ]} →
             {e₁′ : term[ var ] τ₁ cps[ β , γ ]} →
             {e₂′ : var τ₁ → term[ var ] τ₂ cps[ α , β ]} →
             ((x : var τ₁) → Subst (λ y → (e₂ y) x) v (e₂′ x)) →
             Subst e₁ v e₁′ →
             Subst (λ y → NonVal (Let (e₁ y) (e₂ y)))
                   v
                   (NonVal (Let e₁′ e₂′))

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
  DSubst≠ {t = NonVal (App e₁ e₂)} = sApp DSubst≠ DSubst≠
  DSubst≠ {t = NonVal (Reset τ₁ τ₄ τ₃ e)} = sReset DSubst≠
  DSubst≠ {t = NonVal (Let e₁ e₂)} = sLet (λ x → DSubst≠) DSubst≠

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
frame-plug (App₁ e₂) e₁ = NonVal (App e₁ e₂)
frame-plug (App₂ v₁) e₂ = NonVal (App (Val v₁) e₂)
frame-plug {τ₁ = τ₁} {τ₂} {τ₃} Reset e₁ = NonVal (Reset τ₂ τ₁ τ₃ e₁)
frame-plug (Let e₂) e₁ = NonVal (Let e₁ e₂)

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
             {τ₁ τ₂ τ₃ τ₄ τ₅ τ₆ : typ} →
             pframe[ var , τ₁ cps[ τ₂ , τ₃ ]] τ₄ cps[ τ₅ , τ₆ ] →
             term[ var ] τ₁ cps[ τ₂ , τ₃ ] →
             term[ var ] τ₄ cps[ τ₅ , τ₆ ]
pframe-plug (App₁ e₂) e₁ = NonVal (App e₁ e₂)
pframe-plug (App₂ v₁) e₂ = NonVal (App (Val v₁) e₂)
pframe-plug (Let e₂)  e₁ = NonVal (Let e₁ e₂)

data same-pframe {var : typ → Set} :
                 {τ₁ τ₁' τ₂ τ₂' τ₃ τ₃' τ₄ τ₄' τ₅ τ₅' τ₆ τ₆' : typ} →
       pframe[ var , τ₁ cps[ τ₂ , τ₃ ]] τ₄ cps[ τ₅ , τ₆ ] →
       pframe[ var , τ₁' cps[ τ₂' , τ₃' ]] τ₄' cps[ τ₅' , τ₆' ] →
       Set where
  App₁ : {τ₇ τ₈ τ₉ τ₃ τ₃' τ₄ τ₄' τ₅ τ₅' : typ} →
         (e₂ : term[ var ] τ₇ cps[ τ₈ , τ₉ ]) →
         same-pframe {τ₃ = τ₃}{τ₃'}{τ₄}{τ₄'}{τ₅}{τ₅'}
                     (App₁ e₂) (App₁ e₂)
  App₂ : {τ₇ τ₈ τ₉ τ₁₀ τ₃ τ₃' : typ} →
         (v₁ : value[ var ] (τ₈ ⇒ τ₇ cps[ τ₉ , τ₁₀ ]) cps[τ,τ]) →
         same-pframe {τ₃ = τ₃}{τ₃'}
                     (App₂ v₁) (App₂ v₁)
  Let  : {τ₇ τ₈ τ₉ τ₁₀ τ₃ τ₃' : typ} →
         (e₂ : var τ₈ → term[ var ] τ₇ cps[ τ₉ , τ₁₀ ]) →
         same-pframe {τ₃ = τ₃}{τ₃'}
                     (Let e₂) (Let e₂)

-- pure context : for RShift
data pcontext[_,_cps[_,_]]_cps[_,_] (var : typ → Set)
     : typ → typ → typ → typ → typ → typ → Set where
  Hole  : {τ₁ τ₂ τ₃ : typ} →
          pcontext[ var , τ₁ cps[ τ₂ , τ₃ ]] τ₁ cps[ τ₂ , τ₃ ]
  Frame : {τ₁ τ₂ τ₃ τ₄ τ₅ τ₆ τ₇ τ₈ τ₉ : typ} →
          (f : pframe[ var , τ₄ cps[ τ₅ , τ₆ ]] τ₇
                     cps[ τ₈ , τ₉ ]) →
          (e : pcontext[ var , τ₁ cps[ τ₂ , τ₃ ]] τ₄
                       cps[ τ₅ , τ₆ ]) →
          pcontext[ var , τ₁ cps[ τ₂ , τ₃ ]] τ₇ cps[ τ₈ , τ₉ ]

pcontext-plug : {var : typ → Set}
                {τ₁ τ₂ τ₃ τ₄ τ₅ τ₆ : typ} →
                pcontext[ var , τ₁ cps[ τ₂ , τ₃ ]] τ₄
                        cps[ τ₅ , τ₆ ] →
                term[ var ] τ₁ cps[ τ₂ , τ₃ ] →
                term[ var ] τ₄ cps[ τ₅ , τ₆ ]
pcontext-plug Hole        e₁ = e₁
pcontext-plug (Frame f p) e₁ = pframe-plug f (pcontext-plug p e₁)

data same-pcontext {var : typ → Set} :
                   {τ₁ τ₁' τ₂ τ₂' τ₃ τ₃' τ₄ τ₄' τ₅ τ₅' τ₆ τ₆' : typ} →
       pcontext[ var , τ₁ cps[ τ₂ , τ₃ ]] τ₄ cps[ τ₅ , τ₆ ] →
       pcontext[ var , τ₁' cps[ τ₂' , τ₃' ]] τ₄' cps[ τ₅' , τ₆' ] →
       Set where
  Hole  : {τ₁ τ₁' τ₂ τ₂' τ₃ τ₃' : typ} →
          same-pcontext {τ₁ = τ₁}{τ₁'}{τ₂}{τ₂'}{τ₃}{τ₃'}
                        Hole Hole
  Frame : {τ₁ τ₁' τ₂ τ₂' τ₃ τ₃' τ₄ τ₄' τ₅ τ₅' τ₆ τ₆' τ₇ τ₇' τ₈ τ₈' τ₉ τ₉' : typ} →
          {f₁ : pframe[ var , τ₄ cps[ τ₅ , τ₆ ]] τ₇
                      cps[ τ₈ , τ₉ ]} →
          {f₂ : pframe[ var , τ₄' cps[ τ₅' , τ₆' ]] τ₇'
                      cps[ τ₈' , τ₉' ]} →
          same-pframe f₁ f₂ →
          {p₁ : pcontext[ var , τ₁ cps[ τ₂ , τ₃ ]] τ₄
                        cps[ τ₅ , τ₆ ]} →
          {p₂ : pcontext[ var , τ₁' cps[ τ₂' , τ₃' ]] τ₄'
                        cps[ τ₅' , τ₆' ]} →
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
           Reduce (NonVal (App (Val (Fun τ₁ τ e₁)) (Val v₂)))
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
           Reduce (NonVal (Let (Val v₁) e₂)) e₂′
  RReset : {τ₁ τ₂ : typ} →
           {v₁ : value[ var ] τ₁ cps[τ,τ]} →
           Reduce {τ₂ = τ₂} (NonVal (Reset τ₁ τ₁ τ₂ (Val v₁))) (Val v₁)
  RShift : {τ τ₁ τ₂ τ₃ τ₄ τ₅ τ₆ : typ} →
           {v₂ : value[ var ] (τ₃ ⇒ τ₄ cps[ τ , τ ]) ⇒ τ₁ cps[ τ₁ , τ₂ ] cps[τ,τ]} →
           (p₁ : pcontext[ var , τ₃ cps[ τ₄ , τ₂ ]]
                           τ₅ cps[ τ₅ , τ₂ ]) →
           (p₂ : pcontext[ var , τ₃ cps[ τ₄ , τ₄ ]]
                           τ₅ cps[ τ₅ , τ₄ ]) →
           same-pcontext p₁ p₂ →
           Reduce (NonVal (Reset τ₅ τ₂ τ₆
                                 (pcontext-plug p₁ (NonVal (App (Val Shift) (Val v₂))))))
                  (NonVal (Reset τ₁ τ₂ τ₆
                          (NonVal
                            (App (Val v₂)
                                 (Val (Fun τ₄ τ₃ (λ x →
                                     let e = pcontext-plug p₂ (Val (Var x)) in
                                     NonVal (Reset τ₅ τ₄ τ e))))))))
