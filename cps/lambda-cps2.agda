-- λ計算の規則にCPS変換の規則を加える
-- shift reset の規則も導入

module lambda-cps2 where

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

mutual
  pSubstV≠ : {var : typ → Set} {τ₁ τ₂ : typ} →
             {t : value[ var ] τ₁ cps[τ,τ]} →
             {v : value[ var ] τ₂ cps[τ,τ]} →
             SubstVal (λ y → t) v t
  pSubstV≠ {t = Num x} = sNum
  pSubstV≠ {t = Var x} = sVar≠
  pSubstV≠ {t = Fun τ₁ τ₃ e₁} = sFun (λ x → pSubst≠)

  pSubst≠ : {var : typ → Set} {τ₁ τ₂ τ₃ τ₄ : typ} →
            {t : term[ var ] τ₁ cps[ τ₃ , τ₄ ]} →
            {v : value[ var ] τ₂ cps[τ,τ]} →
            Subst (λ y → t) v t      
  pSubst≠ {t = Val x} = sVal pSubstV≠
  pSubst≠ {t = App e₁ e₂} = sApp pSubst≠ pSubst≠
  pSubst≠ {t = Reset τ₁ τ₄ τ₃ e} = sReset pSubst≠
  pSubst≠ {t = Shift τ τ₁ τ₃ τ₄ τ₅ x} = sShift (λ k → pSubst≠)

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

data same-pframe {var : typ → Set} {τ₁ τ₃ τ₅ τ₆ : typ} :
                 {τ τ₇ : typ} →
       pframe[ var , τ cps[ τ₅ , τ₆ ]] τ₁ cps[ τ₃ , τ₆ ] →
       pframe[ var , τ cps[ τ₅ , τ₇ ]] τ₁ cps[ τ₃ , τ₇ ] →
       Set where
  App₁ : {τ₂ τ₄ τ₆ : typ} →
         -- (a₁≤ₐa : a₁ ≤ₐ a) → (a₂≤ₐa : a₂ ≤ₐ a) → (a₃≤ₐa : a₃ ≤ₐ a) →
         -- (c₁ : τ₅ ≠ τ₆ ⇒ a₁ =i) → (c₂ : τ₄ ≠ τ₅ ⇒ a₂ =i) →
         -- (c₃ : τ₃ ≠ τ₄ ⇒ a₃ =i) →
         (e₂ : term[ var ] τ₂ cps[ τ₄ , τ₅ ]) →
         same-pframe (App₁ e₂)
                     (App₁ {τ₆ = τ₆} e₂)
  App₂ : {τ₂ τ₆ : typ} →
         -- (a₁≤ₐa : a₁ ≤ₐ a) → (a₃≤ₐa : a₃ ≤ₐ a) →
         -- (c₁ : τ₅ ≠ τ₇ ⇒ a₁ =i) → (c₃ : τ₃ ≠ τ₅ ⇒ a₃ =i) →
         (v₁ : value[ var ] (τ₂ ⇒ τ₁ cps[ τ₃ , τ₅ ]) cps[τ,τ]) →
         same-pframe (App₂ v₁)
                     (App₂ {τ₅ = τ₆} v₁)

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

-- target type
data cpstyp : Set where
  Nat : cpstyp
  Boolean : cpstyp
  _⇒_ : cpstyp → cpstyp → cpstyp

-- target term
mutual
  data cpsvalue[_] (var : cpstyp → Set) : cpstyp → Set where
    CPSVar : {τ₁ : cpstyp} → var τ₁ → cpsvalue[ var ] τ₁
    CPSNum : ℕ → cpsvalue[ var ] Nat
    CPSFun : {τ₁ τ₂ : cpstyp} →
             (var τ₂ → cpsterm[ var ] τ₁) →
             cpsvalue[ var ] (τ₂ ⇒ τ₁)

  data cpsterm[_] (var : cpstyp → Set) : cpstyp → Set where
    CPSVal : {τ₁ : cpstyp} →
             cpsvalue[ var ] τ₁ →
             cpsterm[ var ] τ₁
    CPSApp : {τ₁ τ₂ : cpstyp} →
             cpsterm[ var ] (τ₂ ⇒ τ₁) →
             cpsterm[ var ] τ₂ →
             cpsterm[ var ] τ₁
    CPSLet : {τ₁ τ₂ : cpstyp} →
             cpsterm[ var ] τ₁ →
             (var τ₁ → cpsterm[ var ] τ₂) →
             cpsterm[ var ] τ₂

-- CPS transformation

cpsT : typ → cpstyp
cpsT Nat = Nat
cpsT Boolean = Boolean
cpsT (τ₂ ⇒ τ₁ cps[ τ₃ , τ₄ ]) =
  cpsT τ₂ ⇒ ((cpsT τ₁ ⇒ cpsT τ₃) ⇒ cpsT τ₄)

mutual
  cpsV : (τ₁ : typ) → {var : cpstyp → Set} →
         value[ var ∘ cpsT ] τ₁ cps[τ,τ] →
         cpsvalue[ var ] (cpsT τ₁)
  cpsV .Nat (Num n) = CPSNum n
  cpsV τ₁   (Var x) = CPSVar x
  cpsV .(τ₂ ⇒ τ₁ cps[ τ₃ , τ₄ ]) (Fun τ₁ τ₂ {τ₃} {τ₄} e) =
    CPSFun (λ x → CPSVal (CPSFun
           (λ k → cpsI′ τ₁ τ₃ τ₄ (e x) (CPSVar k))))

  cpsI : (τ₁ τ₂ τ₃ : typ) → {var : cpstyp → Set} →
         term[ var ∘ cpsT ] τ₁ cps[ τ₂ , τ₃ ] →
         (cpsvalue[ var ] (cpsT τ₁) → cpsterm[ var ] (cpsT τ₂)) → 
         cpsterm[ var ] (cpsT τ₃)
         
  cpsI τ₁ τ₂ .τ₂ (Val v) κ = κ (cpsV τ₁ v)
  cpsI τ₁ τ₂ τ₃  (App {τ₂ = τ₄} {τ₄ = τ₅} {τ₆} e₁ e₂) κ =
    cpsI (τ₄ ⇒ τ₁ cps[ τ₂ , τ₅ ]) τ₆ τ₃
         e₁
         (λ m → cpsI τ₄ τ₅ τ₆
                      e₂
                      (λ n → CPSApp (CPSApp (CPSVal m) (CPSVal n))
                                     (CPSVal (CPSFun (λ a → κ (CPSVar a))))))
                                     -- λκ.(@κ (@ [M] (λm.m)))
  cpsI τ₁ τ₂ .τ₂ (Reset τ₃ .τ₁ .τ₂ e₁) κ = CPSLet (cpsI τ₃ τ₃ τ₁ e₁ (λ m → CPSVal m)) (λ v → κ (CPSVar v))
  cpsI τ₁ τ₂ τ₃ (Shift τ τ₄ .τ₃ .τ₁ .τ₂ e) κ =
    CPSLet (CPSVal (CPSFun (λ a → CPSVal (CPSFun (λ κ′ → CPSApp (CPSVal (CPSVar κ′)) (κ (CPSVar a)))))))
    (λ x → cpsI τ₄ τ₄ τ₃ (e x) (λ m → CPSVal m))

  cpsI′ : (τ₁ τ₂ τ₃ : typ) → {var : cpstyp → Set} →
          term[ var ∘ cpsT ] τ₁ cps[ τ₂ , τ₃ ] →
          cpsvalue[ var ] (cpsT τ₁ ⇒ cpsT τ₂) →
          cpsterm[ var ] (cpsT τ₃)
  cpsI′ τ₁ τ₂ .τ₂ (Val v) k = CPSApp (CPSVal k) (CPSVal (cpsV τ₁ v))
  cpsI′ τ₁ τ₂ τ₃  (App {τ₂ = τ₄} {τ₄ = τ₅} {τ₆} e₁ e₂) k =
    cpsI (τ₄ ⇒ τ₁ cps[ τ₂ , τ₅ ]) τ₆ τ₃
         e₁ (λ m → cpsI τ₄ τ₅ τ₆ e₂ (λ n → CPSApp (CPSApp (CPSVal m) (CPSVal n)) (CPSVal k)))
  cpsI′ τ₁ τ₂ .τ₂ (Reset τ₃ .τ₁ .τ₂ e₁) k =
    -- CPSApp (CPSVal k) (cpsI τ₃ τ₃ τ₁ e₁ (λ m → CPSVal m)) 
    CPSLet (cpsI τ₃ τ₃ τ₁ e₁ (λ m → CPSVal m)) (λ a → CPSApp (CPSVal k) (CPSVal (CPSVar a)))
  cpsI′ τ₁ τ₂ τ₃  (Shift τ τ₄ .τ₃ .τ₁ .τ₂ e) k =
    CPSLet (CPSVal (CPSFun (λ a → CPSVal (CPSFun
                           (λ κ′ → CPSApp (CPSVal (CPSVar κ′))
                           (CPSApp (CPSVal k) (CPSVal(CPSVar a))))))))
           (λ x → cpsI τ₄ τ₄ τ₃ (e x) (λ m → CPSVal m))
    -- CPSLet (CPSVal (CPSFun (λ a → CPSVal (CPSFun (λ κ′ → CPSApp (CPSVal (CPSVar κ′)) (k (CPSVar a)))))))
    -- (λ x → cpsI τ₄ τ₄ τ₃ (e x) (λ m → CPSVal m))

cpsImain : (τ₁ τ₂ τ₃ : typ) → {var : cpstyp → Set} →
       term[ var ∘ cpsT ] τ₁ cps[ τ₂ , τ₃ ] →
       cpsterm[ var ] ((cpsT τ₁ ⇒ cpsT τ₂) ⇒ cpsT τ₃)
cpsImain τ₁ τ₂ τ₃ e = CPSVal (CPSFun (λ k → cpsI′ τ₁ τ₂ τ₃ e (CPSVar k)))

-- cpsframe
data cpsframe[_,_] (var : cpstyp → Set) : cpstyp → cpstyp → Set where
  CPSApp₁ : {τ₁ τ₂ : cpstyp} →
         (e₂ : cpsterm[ var ] τ₂) →
         cpsframe[ var , τ₂ ⇒ τ₁ ] τ₁
  CPSApp₂ : {τ₁ τ₂ : cpstyp} →
         (v₁ : cpsvalue[ var ] (τ₂ ⇒ τ₁)) →
         cpsframe[ var , τ₂ ] τ₁

cpsframe-plug : {var : cpstyp → Set} → {τ₁ τ₂ : cpstyp} →
             cpsframe[ var , τ₂ ] τ₁ →
             cpsterm[ var ] τ₂ →
             cpsterm[ var ] τ₁
cpsframe-plug (CPSApp₁ e₂) e₁ = CPSApp e₁ e₂
cpsframe-plug (CPSApp₂ v₁) e₂ = CPSApp (CPSVal v₁) e₂

-- cpscontext
data cpscontext[_,_] (var : cpstyp → Set) : cpstyp → cpstyp → Set where
  CPSHole  : {τ₁ : cpstyp} →
             cpscontext[ var , τ₁ ] τ₁
  CPSFrame : {τ₁ τ₂ τ₃ : cpstyp} →
             cpsframe[ var , τ₂ ] τ₃ →
             cpscontext[ var , τ₁ ] τ₂ →
             cpscontext[ var , τ₁ ] τ₃

cpscontext-plug : {var : cpstyp → Set} {τ₁ τ₂ : cpstyp} →
                cpscontext[ var , τ₂ ] τ₁ →
                cpsterm[ var ] τ₂ →
                cpsterm[ var ] τ₁
cpscontext-plug CPSHole e₁ = e₁
cpscontext-plug (CPSFrame f p) e₁ = cpsframe-plug f (cpscontext-plug p e₁)

mutual
  data cpsSubstVal {var : cpstyp → Set} : {τ₁ τ₂ : cpstyp} →
                   (var τ₁ → cpsvalue[ var ] τ₂) →
                   cpsvalue[ var ] τ₁ →
                   cpsvalue[ var ] τ₂ → Set where
    sVar= : {τ₁ : cpstyp} {v : cpsvalue[ var ] τ₁} →
            cpsSubstVal (λ x → CPSVar x) v v
    sVar≠ : {τ₁ τ₂ : cpstyp} {v : cpsvalue[ var ] τ₂} {x : var τ₁} →
            cpsSubstVal (λ _ → CPSVar x) v (CPSVar x)
    sNum  : {τ₁ : cpstyp} {v : cpsvalue[ var ] τ₁} {n : ℕ} →
            cpsSubstVal (λ _ → CPSNum n) v (CPSNum n)
    sFun  : {τ τ₁ τ₂ : cpstyp} →
            {e₁ : var τ₁ → var τ → cpsterm[ var ] τ₂} →
            {v : cpsvalue[ var ] τ₁} →
            {e₁′ : var τ → cpsterm[ var ] τ₂} →
            ((x : var τ) → cpsSubst (λ y → (e₁ y) x) v (e₁′ x)) →
            cpsSubstVal (λ y → CPSFun (e₁ y)) v (CPSFun e₁′)

  data cpsSubst {var : cpstyp → Set} : {τ₁ τ₂ : cpstyp} →
                (var τ₁ → cpsterm[ var ] τ₂) →
                cpsvalue[ var ] τ₁ →
                cpsterm[ var ] τ₂ → Set where
    sVal : {τ τ₁ : cpstyp} →
           {v₁ : var τ → cpsvalue[ var ] τ₁} →
           {v : cpsvalue[ var ] τ} →
           {v₁′ : cpsvalue[ var ] τ₁} →
           cpsSubstVal v₁ v v₁′ →
           cpsSubst (λ y → CPSVal (v₁ y)) v (CPSVal v₁′)
    sApp : {τ τ₁ τ₂ : cpstyp} →
           {e₁ : var τ → cpsterm[ var ] (τ₂ ⇒ τ₁)} →
           {e₂ : var τ → cpsterm[ var ] τ₂} →
           {v : cpsvalue[ var ] τ} →
           {e₁′ : cpsterm[ var ] (τ₂ ⇒ τ₁)} →
           {e₂′ : cpsterm[ var ] τ₂} →
           cpsSubst e₁ v e₁′ → cpsSubst e₂ v e₂′ →
           cpsSubst (λ y → CPSApp (e₁ y) (e₂ y)) v (CPSApp e₁′ e₂′)
    sLet : {τ τ₁ τ₂ : cpstyp} →
           {e₁ : var τ₁ → cpsterm[ var ] τ} →
           {e₂ : var τ₁ → var τ → cpsterm[ var ] τ₂} →
           {v : cpsvalue[ var ] τ₁} →
           {e₁′ : cpsterm[ var ] τ} →
           {e₂′ : var τ → cpsterm[ var ] τ₂} →
           ((x : var τ) → cpsSubst (λ y → (e₂ y) x) v (e₂′ x)) →
           ((x : var τ) → cpsSubst (λ y → e₁ y) v e₁′) →
           cpsSubst (λ y → CPSLet (e₁ y) (e₂ y)) v (CPSLet e₁′ e₂′)

data cpsequal {var : cpstyp → Set} :
              {τ₁ : cpstyp} →
              cpsterm[ var ] τ₁ →
              cpsterm[ var ] τ₁ → Set where
  eqBeta   : {τ₁ τ₂ : cpstyp} →
             {e₁ : var τ₂ → cpsterm[ var ] τ₁} →
             {v : cpsvalue[ var ] τ₂} →
             {e₂ : cpsterm[ var ] τ₁} →
             cpsSubst e₁ v e₂ →
             cpsequal (CPSApp (CPSVal (CPSFun e₁)) (CPSVal v)) e₂
  eqLet    : {τ₁ τ₂ : cpstyp} →
             {v₁ : cpsvalue[ var ] τ₁} →
             {e₂ : var τ₁ → cpsterm[ var ] τ₂} →
             {e₂′ : cpsterm[ var ] τ₂} →
             cpsSubst e₂ v₁ e₂′ →
             cpsequal (CPSLet (CPSVal v₁) e₂) e₂′
  eqOmega  : {τ₁ τ₂ : cpstyp} →
             {con : cpscontext[ var , τ₂ ] τ₁} →
             {e₁ : cpsterm[ var ] τ₂} →
             cpsequal (CPSApp (CPSVal (CPSFun (λ x →
                               cpscontext-plug con (CPSVal (CPSVar x))))) e₁)
                      (cpscontext-plug con e₁)
  eqApp₁   : {τ₁ τ₂ : cpstyp} →
             {e₁ : cpsterm[ var ] (τ₂ ⇒ τ₁)} →
             {e₁′ : cpsterm[ var ] (τ₂ ⇒ τ₁)} →
             {e₂ : cpsterm[ var ] τ₂} →
             cpsequal e₁ e₁′ →
             cpsequal (CPSApp e₁ e₂) (CPSApp e₁′ e₂)
  eqApp₂   : {τ₁ τ₂ : cpstyp} →
             {e₁ : cpsterm[ var ] (τ₂ ⇒ τ₁)} →
             {e₂ : cpsterm[ var ] τ₂} →
             {e₂′ : cpsterm[ var ] τ₂} →
             cpsequal e₂ e₂′ →
             cpsequal (CPSApp e₁ e₂) (CPSApp e₁ e₂′)
  eqFun    : {τ₁ τ₂ : cpstyp} →
             {e₁ : var τ₂ → cpsterm[ var ] τ₁} →
             {e₂ : var τ₂ → cpsterm[ var ] τ₁} →
             ((x : var τ₂) → cpsequal (e₁ x) (e₂ x)) →
             cpsequal (CPSVal (CPSFun (λ x → e₁ x)))
                      (CPSVal (CPSFun (λ x → e₂ x)))
  eqLet₁   : {τ₁ τ₂ : cpstyp} →
             {e₁ e₁′ : cpsterm[ var ] τ₁} →
             (e₂ : var τ₁ → cpsterm[ var ] τ₂) →
             cpsequal e₁ e₁′ →
             cpsequal (CPSLet e₁ e₂) (CPSLet e₁′ e₂)
  eqLet₂   : {τ₁ τ₂ : cpstyp} →
             (e₁ : cpsterm[ var ] τ₁) →
             {e₂ e₂′ : var τ₁ → cpsterm[ var ] τ₂} →
             ((x : var τ₁) → cpsequal (e₂ x) (e₂′ x)) →
             cpsequal (CPSLet e₁ e₂) (CPSLet e₁ e₂′)
  eqLet₃   : {τ₁ τ₂ τ₃ : cpstyp} →
             {e₁ : cpsterm[ var ] τ₁} →
             {e₂ : var τ₁ → cpsterm[ var ] (τ₂ ⇒ τ₃)} →
             {e₃ : cpsterm[ var ] τ₂} →
             cpsequal (CPSApp (CPSLet e₁ (λ x → e₂ x)) e₃)
                      (CPSLet e₁ (λ x → CPSApp (e₂ x) e₃))
  eqLetApp : {τ₁ τ₂ : cpstyp} →
             {v₁ : cpsvalue[ var ] τ₁} →
             {e₁ : var τ₁ → cpsterm[ var ] τ₂} →
             cpsequal (CPSLet (CPSVal v₁) (λ x → e₁ x))
                      (CPSApp (CPSVal (CPSFun (λ x → e₁ x))) (CPSVal v₁))
  eqId     : {τ₁ : cpstyp} →
             {e : cpsterm[ var ] τ₁} →
             cpsequal e e
  eqTrans  : {τ₁ : cpstyp} →
             (e₁ e₂ e₃ : cpsterm[ var ] τ₁) →
             cpsequal e₁ e₂ →
             cpsequal e₂ e₃ →
             cpsequal e₁ e₃
  eqTrans′ : {τ₁ : cpstyp} →
             (e₁ e₂ e₃ : cpsterm[ var ] τ₁) →
             cpsequal e₂ e₁ →
             cpsequal e₂ e₃ →
             cpsequal e₁ e₃

data cpsEqual {var : cpstyp → Set} :
           {τ : cpstyp} →
           cpsterm[ var ] τ →
           cpsterm[ var ] τ → Set where
  Eq* : {τ₁ : cpstyp} →
        {e₁ : cpsterm[ var ] τ₁} →
        {e₂ : cpsterm[ var ] τ₁} →
        cpsequal e₁ e₂ →
        cpsEqual e₁ e₂


-- equational reasoning
-- see ≡-Reasoning in Relation.Binary.PropositionalEquality.agda

infix  3 _∎
infixr 2 _⟶⟨_⟩_ _⟵⟨_⟩_ _⟷⟨_⟩_ _≡⟨_⟩_
infix  1 begin_

begin_ : {var : cpstyp → Set} {τ₁ : cpstyp} →
         {e₁ e₂ : cpsterm[ var ] τ₁} →
         cpsequal e₁ e₂ → cpsequal e₁ e₂
begin_ red = red

_⟶⟨_⟩_ : {var : cpstyp → Set} {τ₁ : cpstyp} →
          (e₁ {e₂ e₃} : cpsterm[ var ] τ₁) →
          cpsequal e₁ e₂ → cpsequal e₂ e₃ → cpsequal e₁ e₃
_⟶⟨_⟩_ e₁ {e₂} {e₃} e₁-eq-e₂ e₂-eq-e₃ = eqTrans e₁ e₂ e₃ e₁-eq-e₂ e₂-eq-e₃

_⟵⟨_⟩_ : {var : cpstyp → Set} {τ₁ : cpstyp} →
          (e₁ {e₂ e₃} : cpsterm[ var ] τ₁) →
          cpsequal e₂ e₁ → cpsequal e₂ e₃ → cpsequal e₁ e₃
_⟵⟨_⟩_ e₁ {e₂} {e₃} e₂-eq-e₁ e₂-eq-e₃ = eqTrans′ e₁ e₂ e₃ e₂-eq-e₁ e₂-eq-e₃

_⟷⟨_⟩_ : {var : cpstyp → Set} {τ₁ : cpstyp} →
          (e₁ {e₂ e₃} : cpsterm[ var ] τ₁) →
          cpsequal e₁ e₂ → cpsequal e₂ e₃ → cpsequal e₁ e₃
_⟷⟨_⟩_ e₁ {e₂} {e₃} e₁-eq-e₂ e₂-eq-e₃ = eqTrans e₁ e₂ e₃ e₁-eq-e₂ e₂-eq-e₃

_≡⟨_⟩_ : {var : cpstyp → Set} {τ₁ : cpstyp} →
         (e₁ {e₂ e₃} : cpsterm[ var ] τ₁) → e₁ ≡ e₂ → cpsequal e₂ e₃ →
           cpsequal e₁ e₃
_≡⟨_⟩_ e₁ {e₂} {e₃} refl e₂-eq-e₃ = e₂-eq-e₃

-- _≡₂⟨_⟩_ : {var : cpstyp → Set} {τ₁ τ₂ : cpstyp} →
--           -- (e₁ : var τ₁ → cpsterm[ var ] τ₂) →
--           (e₁ {e₂} : cpsterm[ var ] τ₂) → 
--           {v : cpsvalue[ var ] τ₁} →
--           {e₃ : cpsterm[ var ] τ₂} →
--           e₁ ≡ e₂ → cpsSubst (λ x′ → e₂) v e₃ → cpsSubst (λ x′ → e₃) v e₃
--           -- cpsSubst (λ x → e₁) v e₂ → cpsSubst (λ x → e₂) v e₃ → cpsSubst (λ x → e₁) v e₃
-- _≡₂⟨_⟩_ e₁ {e₂} {e₃} refl e₂-subst-e₃ = e₂-subst-e₃

_∎ : {var : cpstyp → Set} {τ₁ : cpstyp} →
     (e : cpsterm[ var ] τ₁) → cpsequal e e
_∎ e = eqId

-- subst-cont
subst-cont : {var : cpstyp → Set} {τ₁ τ₂ : typ} {τ₄ : cpstyp} →
             (κ₁ : var τ₄ →
                   cpsvalue[ var ] (cpsT τ₁) → cpsterm[ var ] (cpsT τ₂)) →
             (v : cpsvalue[ var ] τ₄) →
             (κ₂ : cpsvalue[ var ] (cpsT τ₁) → cpsterm[ var ] (cpsT τ₂)) → Set
subst-cont {var} {τ₁} {τ₂} {τ₄} κ₁ v κ₂ =
  {v₁ : var τ₄ → cpsvalue[ var ] (cpsT τ₁)} →
  {v₁′ : cpsvalue[ var ] (cpsT τ₁)} →
  cpsSubstVal v₁ v v₁′ →
  cpsSubst (λ y → κ₁ y (v₁ y)) v (κ₂ v₁′)

mutual
  SubstV≠ : {var : cpstyp → Set} {τ₁ τ₂ : cpstyp} →
            {t : cpsvalue[ var ] τ₁} →
            {v : cpsvalue[ var ] τ₂} →
            cpsSubstVal (λ y → t) v t
  SubstV≠ {t = CPSVar x} = sVar≠
  SubstV≠ {t = CPSNum n}  = sNum
  SubstV≠ {t = CPSFun e₁} = sFun (λ x → Subst≠)

  Subst≠ : {var : cpstyp → Set} {τ₁ τ₂ : cpstyp} →
           {t : cpsterm[ var ] τ₁} →
           {v : cpsvalue[ var ] τ₂} →
           cpsSubst (λ y → t) v t
  Subst≠ {t = CPSVal x} = sVal SubstV≠
  Subst≠ {t = CPSApp e₁ e₂} = sApp Subst≠ Subst≠
  Subst≠ {t = CPSLet e₁ e₂} = sLet (λ x → Subst≠) (λ x → Subst≠)

mutual
  eSubstV : {var : cpstyp → Set} {τ₁ τ : typ} →
            {v₁  : var (cpsT τ) → value[ var ∘ cpsT ] τ₁ cps[τ,τ]} →
            {v₁′ : value[ var ∘ cpsT ] τ₁ cps[τ,τ]} →
            {v   : value[ var ∘ cpsT ] τ cps[τ,τ]} →
            SubstVal v₁ v v₁′ →
            cpsSubstVal (λ y → cpsV τ₁ {var = var} (v₁ y)) (cpsV τ v)
                        (cpsV τ₁ v₁′)
  eSubstV SubstVal.sVar= = cpsSubstVal.sVar=
  eSubstV SubstVal.sVar≠ = cpsSubstVal.sVar≠
  eSubstV SubstVal.sNum  = cpsSubstVal.sNum
  eSubstV {var} {τ₁} {τ = τ₂} {v₁} {v₁′} {v} (sFun sub) = 
    sFun (λ x → sVal (sFun (λ k → ekSubst′ k (sub x))))

  eκSubst : {var : cpstyp → Set} {τ₁ τ₂ τ₃ τ : typ} →
             {e₁ : var (cpsT τ) →
                   term[ var ∘ cpsT ] τ₁ cps[ τ₂ , τ₃ ]} →
             {e₂ : term[ var ∘ cpsT ] τ₁ cps[ τ₂ , τ₃ ]} →
             {v₂ : value[ var ∘ cpsT ] τ cps[τ,τ]} →
             {κ₁ : var (cpsT τ) → cpsvalue[ var ] (cpsT τ₁) → cpsterm[ var ] (cpsT τ₂)} →
             {κ₂ : cpsvalue[ var ] (cpsT τ₁) → cpsterm[ var ] (cpsT τ₂)} →
             Subst e₁ v₂ e₂ →
             subst-cont κ₁ (cpsV τ v₂) κ₂ →
             cpsSubst (λ x → cpsI τ₁ τ₂ τ₃ {var = var} (e₁ x) (κ₁ x))
                      (cpsV τ v₂)
                      (cpsI τ₁ τ₂ τ₃ e₂ κ₂)
  eκSubst (sVal subv)      eq = eq (eSubstV subv)
  eκSubst (sApp sub₁ sub₂) eq =
    eκSubst sub₁ λ m → eκSubst sub₂
                  λ n → sApp (sApp (sVal m) (sVal n)) (sVal (sFun λ a → eq sVar≠))
  eκSubst (sReset sub)    eq = sLet (λ c → eq sVar≠) (λ c → eκSubst sub (λ m → sVal m))                   
  eκSubst (sShift sub)    eq = sLet (λ c → eκSubst (sub c) (λ m → sVal m))
                                     (λ c → sVal (sFun (λ a →
                                             sVal (sFun (λ κ' → sApp (sVal sVar≠) (eq sVar≠))))))



-- Goal: cpsSubst (λ y → cpsI′ τ₁ τ₂ τ₃ (e₁ y) (CPSVar k)) (cpsV τ v₂)
--       (_e₁′_1459 k)
-- ————————————————————————————————————————————————————————————
-- k    : var (cpsT τ₁ ⇒ cpsT τ₂)
-- e₂   : term[ (λ {x} → var) ∘ cpsT ] τ₁ cps[ τ₂ , τ₃ ]
-- v₂   : value[ (λ {x} → var) ∘ cpsT ] τ cps[τ,τ]
-- e₁   : ((λ {x} → var) ∘ cpsT) τ →
--        term[ (λ {x} → var) ∘ cpsT ] τ₁ cps[ τ₂ , τ₃ ]
     
  -- ([e₁]′ @ k)[v/y] = [e₂]′ @ k
  ekSubst′ : {var : cpstyp → Set} {τ₁ τ₂ τ₃ τ : typ} →
             {e₁ : var (cpsT τ) →
                   term[ var ∘ cpsT ] τ₁ cps[ τ₂ , τ₃ ]} →
             {e₂ : term[ var ∘ cpsT ] τ₁ cps[ τ₂ , τ₃ ]} →
             {v₂ : value[ var ∘ cpsT ] τ cps[τ,τ]} →
             (k : var (cpsT τ₁ ⇒ cpsT τ₂)) → 
             Subst e₁ v₂ e₂ →
             cpsSubst (λ x → cpsI′ τ₁ τ₂ τ₃ {var = var} (e₁ x) (CPSVar k))
                      (cpsV τ v₂)
                      (cpsI′ τ₁ τ₂ τ₃ e₂ (CPSVar k))
  ekSubst′ k (sVal sub)        = sApp (sVal sVar≠) (sVal (eSubstV sub))
  ekSubst′ k (sApp sub₁ sub₂) = eκSubst sub₁
                                        (λ m → eκSubst sub₂
                                        (λ n → sApp (sApp (sVal m) (sVal n)) (sVal sVar≠)))
  ekSubst′ k (sReset sub) = sLet (λ c → sApp (sVal sVar≠) (sVal sVar≠))
                                 (λ c → eκSubst sub (λ m → sVal m))                                        
  ekSubst′ k (sShift sub) = sLet (λ c → eκSubst (sub c) (λ m → sVal m))
                                 (λ c → sVal (sFun (λ a →
                                         sVal (sFun (λ κ' → sApp (sVal sVar≠)
                                                                  (sApp (sVal sVar≠) (sVal sVar≠)))))))

eSubst : {var : cpstyp → Set} {τ₁ τ₂ τ₃ τ : typ} →
           {e₁ : var (cpsT τ) →
                 term[ var ∘ cpsT ] τ₁ cps[ τ₂ , τ₃ ]} →
           {e₂ : term[ var ∘ cpsT ] τ₁ cps[ τ₂ , τ₃ ]} →
           {v : value[ var ∘ cpsT ] τ cps[τ,τ]} →
           {κ : cpsvalue[ var ] (cpsT τ₁) → cpsterm[ var ] (cpsT τ₂)} →
           Subst e₁ v e₂ →
           subst-cont (λ x → κ) (cpsV τ v) κ →
           cpsSubst (λ x → cpsI τ₁ τ₂ τ₃ {var = var} (e₁ x) κ)
                    (cpsV τ v)
                    (cpsI τ₁ τ₂ τ₃ e₂ κ)
eSubst (sVal subv) eq = eq (eSubstV subv)
eSubst (sApp sub₁ sub₂) eq =
  eκSubst sub₁ (λ m → eκSubst sub₂ (λ n → sApp (sApp (sVal m) (sVal n)) (sVal (sFun (λ a → eq sVar≠)))))
eSubst (sShift sub) eq = sLet (λ c → eκSubst (sub c) (λ m → sVal m))
                              λ c → sVal (sFun (λ a → sVal (sFun (λ κ′ → sApp (sVal sVar≠) (eq sVar≠)))))
eSubst (sReset sub) eq = sLet (λ c → eq sVar≠) (λ c → eSubst sub (λ m → sVal m))

-- eSubst : {var : cpstyp → Set} {τ₁ τ₂ τ₃ τ : typ} →
--          {e₁ : var (cpsT τ) →
--                  term[ var ∘ cpsT ] τ₁ cps[ τ₂ , τ₃ ]} →
--          {e₂ : term[ var ∘ cpsT ] τ₁ cps[ τ₂ , τ₃ ]} →
--          {v : value[ var ∘ cpsT ] τ cps[τ,τ]} →
--          {κ : cpsvalue[ var ] (cpsT τ₁) → cpsterm[ var ] (cpsT τ₂)} →
--          Subst e₁ v e₂ →
--          -- subst-cont (λ x → κ) (cpsV τ v) κ →
--          cpsequal (κ₁ (cpsV τ₁ v)) (κ₂ (cpsV τ₁ v))) →
--          cpsSubst (λ x → cpsI τ₁ τ₂ τ₃ {var = var} (e₁ x) κ)
--                   (cpsV τ v)
--                   (cpsI τ₁ τ₂ τ₃ e₂ κ)


-- eκSubst (sVal subv)      eq = eq (eSubstV subv)
-- eκSubst (sApp sub₁ sub₂) eq =
--   eκSubst sub₁ λ m → eκSubst sub₂
--                   λ n → sApp (sApp (sVal m) (sVal n)) (sVal (sFun λ a → eq sVar≠))
--   eκSubst (sReset sub)    eq = sLet (λ c → eq sVar≠) (λ c → eκSubst sub (λ m → sVal m))                   
--   eκSubst (sShift sub)    eq = sLet (λ c → eκSubst (sub c) (λ m → sVal m))
--                                      (λ c → sVal (sFun (λ a →

{----------------SCHEMATIC----------------}

schematic : {var : cpstyp → Set} {τ₁ τ₂ : typ} →
            (κ : cpsvalue[ var ] (cpsT τ₁) →
                  cpsterm[ var ] (cpsT τ₂)) → Set
schematic {var} {τ₁} κ =
  (v : cpsvalue[ var ] (cpsT τ₁)) →
  cpsSubst (λ y → κ (CPSVar y)) v (κ v)

schematic′ : {var : cpstyp → Set} {τ₁ τ₂ : typ} {τ : cpstyp} →
             (κ : cpsvalue[ var ] τ →
                   cpsvalue[ var ] (cpsT τ₁) → cpsterm[ var ] (cpsT τ₂)) → Set
schematic′ {var} {τ₁} {τ₂} {τ} κ =
  {v : cpsvalue[ var ] τ} →
  (x : cpsvalue[ var ] (cpsT τ₁)) →
  cpsSubst (λ y → κ (CPSVar y) x) v (κ v x)

schematicV : {var : cpstyp → Set} {τ₁ τ₂ : typ} →
            (κ : cpsvalue[ var ] (cpsT τ₁) →
                  cpsterm[ var ] (cpsT τ₂)) → Set
schematicV {var} {τ₁} {τ₂} κ =
  (v : value[ var ∘ cpsT ] τ₁ cps[τ,τ]) →
  cpsSubst (λ y → κ (CPSVar y)) (cpsV τ₁ v) (κ (cpsV τ₁ v))


-- C-c C-x C-h -> C-c C-c e
κSubst : {var : cpstyp → Set} {τ₁ τ₂ τ₃ : typ} {τ : cpstyp} →
         (e : term[ var ∘ cpsT ] τ₁ cps[ τ₂ , τ₃ ]) →
         -- (e : term[ var ∘ cpsT ] τ₄ ⇒ τ₁ cps[ τ₂ , τ₃ ]) →         
         {v : cpsvalue[ var ] τ} → 
         -- {v : cpsvalue[ var ] (cpsT τ₁ ⇒ cpsT τ₂)} →
         (κ : cpsvalue[ var ] τ →
              cpsvalue[ var ] (cpsT τ₁) → cpsterm[ var ] (cpsT τ₂)) →
         schematic′ κ →
         cpsSubst (λ k → cpsI τ₁ τ₂ τ₃ e (κ (CPSVar k))) v (cpsI τ₁ τ₂ τ₃ e (κ v))
κSubst {var} {τ₁} {τ₂} {.τ₂} {τ} (Val {τ₁ = .τ₁} {τ₂ = .τ₂} v) κ sch-κ = sch-κ (cpsV τ₁ v)
κSubst {var} {τ₁} {τ₂} {τ₃} {τ} (App {τ₁ = .τ₁} {τ₂ = τ₄} {τ₃ = .τ₂} {τ₄ = τ₅} {τ₅ = τ₆} {τ₆ = .τ₃} e₁ e₂) {v} κ sch-κ =
  κSubst e₁ (λ v' → (λ m →
            cpsI τ₄ τ₅ τ₆ e₂
            (λ n →
               CPSApp (CPSApp (CPSVal m) (CPSVal n))
               (CPSVal (CPSFun (λ a → κ v' (CPSVar a))))))) (λ v₁ → 
  κSubst e₂ (λ v' → (λ n →
            CPSApp (CPSApp (CPSVal v₁) (CPSVal n))
            (CPSVal (CPSFun (λ a → κ v' (CPSVar a)))))) λ v₂ → sApp Subst≠ (sVal (sFun (λ k' → sch-κ (CPSVar k')))))
            
κSubst {var} {.τ₂} {.τ₃} {τ₃} {τ} (Reset τ₁ τ₂ τ₃ e) {v} κ sch-κ =
  sLet (λ k' → sch-κ (CPSVar k')) (λ m → Subst≠)

κSubst {var} {.τ₄} {.τ₅} {.τ₃} {τ} (Shift τ₁ τ₂ τ₃ τ₄ τ₅ e) {v} κ sch-κ =
  sLet (λ k' → Subst≠)
       λ v' → sVal (sFun (λ a → sVal (sFun (λ κ′ → sApp Subst≠ (sch-κ (CPSVar a))))))


-- k[v/k] = v ⟶ [e]′@(k[v/k]) = [e′]′@(k[v/k]) = [e′]′@v
kSubst′ : {var : cpstyp → Set} {τ₁ τ₂ τ₃ : typ} →
          (e : term[ var ∘ cpsT ] τ₁ cps[ τ₂ , τ₃ ]) →
          {v : cpsvalue[ var ] (cpsT τ₁ ⇒ cpsT τ₂)} →
          cpsSubst (λ k → cpsI′ τ₁ τ₂ τ₃ e (CPSVar k)) v (cpsI′ τ₁ τ₂ τ₃ e v)

kSubst′ (Val v) = sApp (sVal sVar=) (sVal SubstV≠)
kSubst′ {var} {τ₁} {τ₂} {τ₃} (App {τ₁ = .τ₁} {τ₂ = τ₄} {τ₃ = .τ₂} {τ₄ = τ₅} {τ₅ = τ₆} {τ₆ = .τ₃} e₁ e₂) =
  κSubst e₁ (λ v' → λ m →
                     cpsI τ₄ τ₅ τ₆ e₂
                     (λ n → CPSApp (CPSApp (CPSVal m) (CPSVal n)) (CPSVal v'))) λ v₁ → 
  κSubst e₂ (λ v' → (λ n → CPSApp (CPSApp (CPSVal v₁) (CPSVal n)) (CPSVal v'))) λ v₂ → sApp Subst≠ (sVal sVar=)
kSubst′ (Reset τ₁ τ₂ τ₃ e) =
  sLet (λ k' → sApp (sVal sVar=) Subst≠) (λ m → Subst≠)
kSubst′ (Shift τ₁ τ₂ τ₃ τ₄ τ₅ e) =
  sLet (λ m  → Subst≠)
       (λ k' → sVal (sFun (λ a → sVal (sFun (λ κ′ → sApp Subst≠ (sApp (sVal sVar=) Subst≠))))))             

-- @ [e]′ (λv.@'κ v) ⟶* @' [e] κ
cpsEtaEta′ : {var : cpstyp → Set} → {τ₁ τ₂ τ₃ : typ} →
             (e   : term[ var ∘ cpsT ] τ₁ cps[ τ₂ , τ₃ ]) →
             (κ  : cpsvalue[ var ] (cpsT τ₁) → cpsterm[ var ] (cpsT τ₂)) →
             schematicV κ → 
             cpsequal (cpsI′ τ₁ τ₂ τ₃ e (CPSFun (λ a → κ (CPSVar a)))) (cpsI τ₁ τ₂ τ₃ e κ)
             
cpsEtaEta′ {τ₁ = τ₁} {τ₂} {.τ₂} (Val {τ₁ = .τ₁} {τ₂ = .τ₂} v) κ sche =
  begin
    cpsI′ τ₁ τ₂ τ₂ (Val v) (CPSFun (λ a → κ (CPSVar a)))
  ≡⟨ refl ⟩
    CPSApp (CPSVal (CPSFun (λ a → κ (CPSVar a))))
           (CPSVal (cpsV τ₁ v))    
  ⟶⟨ eqBeta (sche v) ⟩
    κ (cpsV τ₁ v)
  ⟶⟨ eqId ⟩
    cpsI τ₁ τ₂ τ₂ (Val v) κ
  ∎

cpsEtaEta′ {τ₁ = τ₁} {τ₂} {τ₃} (App {τ₁ = .τ₁} {τ₂ = τ₄} {τ₃ = .τ₂} {τ₄ = τ₅} {τ₅ = τ₆} {τ₆ = .τ₃} e₁ e₂) κ sche =
  begin
    cpsI′ τ₁ τ₂ τ₃ (App e₁ e₂) (CPSFun (λ a → κ (CPSVar a)))
  ≡⟨ refl ⟩
    cpsI (τ₄ ⇒ τ₁ cps[ τ₂ , τ₅ ]) τ₆ τ₃ e₁
    (λ m → cpsI τ₄ τ₅ τ₆ e₂
           λ n → CPSApp (CPSApp (CPSVal m) (CPSVal n)) (CPSVal (CPSFun (λ a → κ (CPSVar a)))))
  ⟶⟨ eqId ⟩
    cpsI τ₁ τ₂ τ₃ (App e₁ e₂) κ
  ∎
  
cpsEtaEta′ {τ₁ = .τ₂} {.τ₃} {.τ₃} (Reset τ₁ τ₂ τ₃ e) κ sche =
  begin
    cpsI′ τ₂ τ₃ τ₃ (Reset τ₁ τ₂ τ₃ e) (CPSFun (λ a → κ (CPSVar a)))
  ≡⟨ refl ⟩
    CPSLet (cpsI τ₁ τ₁ τ₂ e (λ m → CPSVal m))
           (λ c → CPSApp (CPSVal (CPSFun λ a → κ (CPSVar a))) (CPSVal (CPSVar c)))
  ⟶⟨ eqLet₂ (cpsI τ₁ τ₁ τ₂ e CPSVal) (λ k' → eqBeta (sche (Var k'))) ⟩
    CPSLet (cpsI τ₁ τ₁ τ₂ e (λ m → CPSVal m))
           (λ c → κ (CPSVar c))
  ⟶⟨ eqId ⟩
    cpsI τ₂ τ₃ τ₃ (Reset τ₁ τ₂ τ₃ e) κ
  ∎

cpsEtaEta′ {τ₁ = .τ₃} {.τ₄} {.τ₂} (Shift τ τ₁ τ₂ τ₃ τ₄ e) κ sche =
  begin
    cpsI′ τ₃ τ₄ τ₂ (Shift τ τ₁ τ₂ τ₃ τ₄ e) (CPSFun (λ a → κ (CPSVar a)))
  ≡⟨ refl ⟩
    CPSLet (CPSVal (CPSFun (λ a → CPSVal (CPSFun
           (λ κ′ → CPSApp (CPSVal (CPSVar κ′))
                           (CPSApp (CPSVal (CPSFun (λ a → κ (CPSVar a)))) -- ????
                                   (CPSVal (CPSVar a))))))))
      (λ c → cpsI τ₁ τ₁ τ₂ (e c) (λ m → CPSVal m))
  ⟶⟨ eqLet₁ (λ c → cpsI τ₁ τ₁ τ₂ (e c) (λ m → CPSVal m))
      (eqFun λ a → eqFun (λ κ′ → eqApp₂ (eqBeta (sche (Var a)))) ) ⟩
    CPSLet (CPSVal (CPSFun (λ a → CPSVal (CPSFun
           (λ κ′ → CPSApp (CPSVal (CPSVar κ′)) (κ (CPSVar a)))))))
      (λ c → cpsI τ₁ τ₁ τ₂ (e c) (λ m → CPSVal m))
  ⟶⟨ eqId ⟩
    cpsI τ₃ τ₄ τ₂ (Shift τ τ₁ τ₂ τ₃ τ₄ e) κ
  ∎

correctContI : {var : cpstyp → Set} → {τ₁ τ₂ τ₃ : typ} →
               {e₁ : term[ var ∘ cpsT ] τ₁ cps[ τ₂ , τ₃ ]} →
               (κ₁ : cpsvalue[ var ] (cpsT τ₁) → cpsterm[ var ] (cpsT τ₂)) →
               (κ₂ : cpsvalue[ var ] (cpsT τ₁) → cpsterm[ var ] (cpsT τ₂)) →
               schematic {var} {τ₁} {τ₂} κ₁ →
               schematic {var} {τ₁} {τ₂} κ₂ →
               ((v : value[ var ∘ cpsT ] τ₁ cps[τ,τ]) →
                cpsequal (κ₁ (cpsV τ₁ v)) (κ₂ (cpsV τ₁ v))) →
               cpsequal (cpsI τ₁ τ₂ τ₃ e₁ κ₁) (cpsI τ₁ τ₂ τ₃ e₁ κ₂)
correctContI {var} {τ₁} {τ₂} {.τ₂} {Val {τ₁ = .τ₁} {τ₂ = .τ₂} x} κ₁ κ₂ sche₁ sche₂ eq = eq x
correctContI {var} {τ₁} {τ₂} {τ₃}
             {App {τ₁ = .τ₁} {τ₂ = τ₄} {τ₃ = .τ₂} {τ₄ = τ₅} {τ₅ = τ₆} {τ₆ = .τ₃} e₁ e₂} κ₁ κ₂ sche₁ sche₂ eq =
  begin
    cpsI τ₁ τ₂ τ₃ (App e₁ e₂) κ₁
  ≡⟨ refl ⟩
    cpsI (τ₄ ⇒ τ₁ cps[ τ₂ , τ₅ ]) τ₆ τ₃ e₁
         (λ m → cpsI τ₄ τ₅ τ₆ e₂
                     λ n → CPSApp (CPSApp (CPSVal m) (CPSVal n)) (CPSVal (CPSFun (λ a → κ₁ (CPSVar a)))))
  ⟶⟨ correctContI {e₁ = e₁}
                    (λ m → cpsI τ₄ τ₅ τ₆ e₂
                                (λ n → CPSApp (CPSApp (CPSVal m) (CPSVal n)) (CPSVal (CPSFun (λ a → κ₁ (CPSVar a))))))
                    (λ m → cpsI τ₄ τ₅ τ₆ e₂
                                (λ n → CPSApp (CPSApp (CPSVal m) (CPSVal n)) (CPSVal (CPSFun (λ a → κ₂ (CPSVar a))))))
                    (λ x → κSubst e₂ (λ v → λ n → CPSApp (CPSApp (CPSVal v) (CPSVal n)) (CPSVal (CPSFun (λ a → κ₁ (CPSVar a)))))
                                   λ x₁ → sApp (sApp (sVal sVar=) Subst≠) (sVal (sFun (λ a → Subst≠))))
                    (λ x → κSubst e₂ (λ v → λ n → CPSApp (CPSApp (CPSVal v) (CPSVal n)) (CPSVal (CPSFun (λ a → κ₂ (CPSVar a)))))
                                   λ x₁ → sApp (sApp (sVal sVar=) Subst≠) (sVal (sFun (λ a → Subst≠))))
                    (λ v → correctContI {e₁ = e₂}
                                         (λ n → CPSApp (CPSApp (CPSVal (cpsV (τ₄ ⇒ τ₁ cps[ τ₂ , τ₅ ]) v)) (CPSVal n))
                                                        (CPSVal (CPSFun (λ a → κ₁ (CPSVar a)))))
                                         (λ n → CPSApp (CPSApp (CPSVal (cpsV (τ₄ ⇒ τ₁ cps[ τ₂ , τ₅ ]) v)) (CPSVal n))
                                                        (CPSVal (CPSFun (λ a → κ₂ (CPSVar a)))))
                                         (λ x′ → sApp (sApp (sVal SubstV≠) (sVal sVar=)) (sVal (sFun (λ a → Subst≠))))
                                         (λ x′ → sApp (sApp (sVal SubstV≠) (sVal sVar=)) (sVal (sFun (λ a → Subst≠))))
                                         λ v₁ → eqApp₂ (eqFun (λ a → eq (Var a)))) ⟩                     
    cpsI (τ₄ ⇒ τ₁ cps[ τ₂ , τ₅ ]) τ₆ τ₃ e₁
         (λ m → cpsI τ₄ τ₅ τ₆ e₂
                     (λ n → CPSApp (CPSApp (CPSVal m) (CPSVal n)) (CPSVal (CPSFun (λ a → κ₂ (CPSVar a))))))
  ≡⟨ refl ⟩
    cpsI τ₁ τ₂ τ₃ (App e₁ e₂) κ₂
  ∎
correctContI {var} {.τ₂} {.τ₃} {τ₃} {Reset τ₁ τ₂ τ₃ e₁} κ₁ κ₂ sche₁ sche₂ eq =
  eqLet₂ (cpsI τ₁ τ₁ τ₂ e₁ (λ m → CPSVal m)) (λ x → eq (Var x))
  
correctContI {var} {.τ₃} {.τ₄} {.τ₂} {Shift τ τ₁ τ₂ τ₃ τ₄ e₁} κ₁ κ₂ sche₁ sche₂ eq =
  eqLet₁ (λ c → cpsI τ₁ τ₁ τ₂ (e₁ c) λ m → CPSVal m)
         (eqFun (λ a → eqFun (λ κ′ → eqApp₂ (eq (Var a)))))

-- correctContI′ : {var : cpstyp → Set} → {τ₁ τ₂ τ₃ : typ} →
--                 {e₁ : term[ var ∘ cpsT ] τ₁ cps[ τ₂ , τ₃ ]} →
--                 cpsequal {!!} (cpsI′ {!!} {!!} {!!} {!!} {!!})
-- correctContI′ = {!!}



-- Goal: Subst (λ x → pcontext-plug τ₁ p₂′ (Val (Var x))) (Var a)
--       (pcontext-plug τ₁ p₂′ (Val (Var a)))
-- ————————————————————————————————————————————————————————————
-- k   : var ((cpsT τ₆ ⇒ ((cpsT τ₄ ⇒ cpsT τ₅) ⇒ cpsT τ₈)) ⇒ cpsT τ₇)
-- κ′  : var (cpsT τ₂ ⇒ cpsT α)
-- a   : var (cpsT τ₁)
-- e₁  : var (cpsT τ₁ ⇒ ((cpsT τ₂ ⇒ cpsT α) ⇒ cpsT α)) →
--       term[ (λ {x} → var) ∘ cpsT ] τ cps[ τ , τ₃ ]
-- p₂′ : pcontext[ (λ {x} → var) ∘ cpsT , τ₁ cps[ τ₂ , τ₂ ]]
--       τ₆ ⇒ τ₄ cps[ τ₅ , τ₈ ] cps[ τ₇ , τ₂ ]
-- p₁′ : pcontext[ (λ {x} → var) ∘ cpsT , τ₁ cps[ τ₂ , τ₃ ]]
--       τ₆ ⇒ τ₄ cps[ τ₅ , τ₈ ] cps[ τ₇ , τ₃ ]

subst-context : {var : typ → Set} {τ₂ τ₃ τ₄ τ₀ : typ} →
                (con : pcontext[ var , τ₀ cps[ τ₂ , τ₂ ]] τ₄ cps[ τ₃ , τ₂ ]) →
                (v : value[ var ] τ₀ cps[τ,τ]) →
                Subst (λ x → pcontext-plug τ₀ con (Val (Var x)))
                      v
                      (pcontext-plug τ₀ con (Val v))
subst-context {var} {τ₂} {.τ₂} {τ₄} {.τ₄} (Hole {τ₁ = .τ₄} {τ₂ = .τ₂} {τ₃ = .τ₂}) v = sVal sVar=
subst-context {var} {τ₂} {τ₃} {τ₄} {τ₀}
              (Frame {τ₁ = .τ₀} {τ₂ = .τ₂} {τ₃ = .τ₂}
                     {τ₄ = .(τ₅ ⇒ τ₄ cps[ τ₃ , τ₇ ])} {τ₅ = τ₆} {τ₆ = .τ₄} {τ₇ = .τ₃}
                     (App₁ {τ₁ = .τ₄} {τ₂ = τ₅} {τ₃ = .τ₃} {τ₄ = τ₇} {τ₅ = .τ₆} {τ₆ = .τ₂} e₂) con′)
              v = sApp (subst-context con′ v) pSubst≠
subst-context {var} {τ₂} {τ₃} {τ₄} {τ₀}
              (Frame {τ₁ = .τ₀} {τ₂ = .τ₂} {τ₃ = .τ₂} {τ₄ = τ₅} {τ₅ = τ₆} {τ₆ = .τ₄} {τ₇ = .τ₃}
                     (App₂ {τ₁ = .τ₄} {τ₂ = .τ₅} {τ₃ = .τ₃} {τ₄ = .τ₆} {τ₅ = .τ₂} v₁) con′)
              v = sApp (sVal pSubstV≠) (subst-context con′ v) 
              

shift-lemma : ∀ {τ τ₁ τ₂ τ₃ τ₄ τ₅ α} {var : cpstyp → Set}
                (p₁ : pcontext[ var ∘ cpsT , τ₁ cps[ τ₂ , τ₃ ]]
                      τ₄ cps[ τ₅ , τ₃ ])
                (p₂ : pcontext[ var ∘ cpsT , τ₁ cps[ τ₂ , τ₂ ]]
                      τ₄ cps[ τ₅ , τ₂ ]) →
                same-pcontext p₁ p₂ →
                (e₁ : var (cpsT (τ₁ ⇒ τ₂ cps[ α , α ])) →
                   term[ var ∘ cpsT ] τ cps[ τ , τ₃ ])
                (κ : cpsvalue[ var ] (cpsT τ₄) → cpsterm[ var ] (cpsT τ₅))
                (sch : schematic {var} {τ₄} {τ₅} κ) →
                cpsequal (cpsI τ₄ τ₅ τ₃
                          (pcontext-plug τ₁ p₁ (Shift α τ τ₃ τ₁ τ₂ e₁)) κ)
                         (cpsI τ₄ τ₅ τ₃
                           (App (Val (Fun τ₄ τ₁
                                     (λ x → pcontext-plug τ₁ p₂ (Val (Var x)))))
                                            (Shift α τ τ₃ τ₁ τ₂ e₁)) κ)
<<<<<<< HEAD

=======
>>>>>>> 85b17510afd0f45f67318dad8b3c63a93f148bc5
shift-lemma {τ} {τ₁} {τ₂} {τ₃} {.τ₁} {.τ₂} {α} {var}
  .(Hole {_} {τ₁} {τ₂} {τ₃})
  .(Hole {_} {τ₁} {τ₂} {τ₂})
  Hole
  e₁ κ sch =
  begin
    cpsI τ₁ τ₂ τ₃ (pcontext-plug τ₁ Hole (Shift α τ τ₃ τ₁ τ₂ e₁)) κ
  ≡⟨ refl ⟩
    cpsI τ₁ τ₂ τ₃ (Shift α τ τ₃ τ₁ τ₂ e₁) κ
  ≡⟨ refl ⟩
    CPSLet (CPSVal (CPSFun (λ a → CPSVal (CPSFun
                           (λ κ′ →
                           CPSApp (CPSVal (CPSVar κ′)) (κ (CPSVar a)))))))
           (λ c → cpsI τ τ τ₃ (e₁ c) (λ m → CPSVal m))
  ⟵⟨ eqLet₁ (λ x → cpsI τ τ τ₃ (e₁ x) λ m → CPSVal m)
             (eqFun (λ x → eqFun (λ x₁ → eqApp₂ (eqBeta (sch (CPSVar x)))))) ⟩
    CPSLet (CPSVal (CPSFun (λ a → CPSVal (CPSFun
                           (λ κ′ →
                           CPSApp (CPSVal (CPSVar κ′))
                                  (CPSApp (CPSVal (CPSFun (λ v → κ (CPSVar v))))
                                          (CPSVal (CPSVar a)))))))) 
           (λ c → cpsI τ τ τ₃ (e₁ c) (λ m → CPSVal m))
  ⟵⟨ eqLet₁ (λ x → cpsI τ τ τ₃ (e₁ x) (λ m → CPSVal m))
              (eqFun (λ x → eqFun (λ x₁ → eqApp₂ (eqBeta (sApp (sVal sVar=) (sVal sVar≠)))))) ⟩
    CPSLet (CPSVal (CPSFun (λ a → CPSVal (CPSFun
                           (λ κ′ →
                           CPSApp (CPSVal (CPSVar κ′))
                                  (CPSApp (CPSVal (CPSFun (λ k → CPSApp (CPSVal (CPSVar k))
                                                                         (CPSVal (CPSVar a)))))
                                          (CPSVal (CPSFun λ v → κ (CPSVar v)))))))))
           (λ c → cpsI τ τ τ₃ (e₁ c) (λ m → CPSVal m))
  ⟵⟨ eqLet₁ (λ x → cpsI τ τ τ₃ (e₁ x) (λ m → CPSVal m))
              (eqFun (λ x → eqFun (λ x₁ → eqApp₂ (eqApp₁ (eqBeta (sVal (sFun (λ x → sApp (sVal sVar≠) (sVal sVar=))))))))) ⟩
    CPSLet (CPSVal (CPSFun (λ a → CPSVal (CPSFun
                           (λ κ′ →
                           CPSApp (CPSVal (CPSVar κ′))
                                  (CPSApp (CPSApp (CPSVal (CPSFun (λ x → CPSVal (CPSFun
                                                                  (λ k → CPSApp (CPSVal (CPSVar k))
                                                                                 (CPSVal (CPSVar x)))))))
                                                  (CPSVal (CPSVar a)))
                                          (CPSVal (CPSFun (λ v → κ (CPSVar v))))))))))
           (λ c → cpsI τ τ τ₃ (e₁ c) (λ m → CPSVal m))
  ≡⟨ refl ⟩
    CPSLet (CPSVal (CPSFun (λ a → CPSVal (CPSFun
                           (λ κ′ →
                           CPSApp (CPSVal (CPSVar κ′))
                                  (CPSApp (CPSApp (CPSVal (CPSFun (λ x → CPSVal (CPSFun
                                                                  (λ k → cpsI′ τ₁ τ₂ τ₂ (Val (Var x)) (CPSVar k))))))
                                                  (CPSVal (CPSVar a)))
                                          (CPSVal (CPSFun (λ v → κ (CPSVar v))))))))))
           (λ c → cpsI τ τ τ₃ (e₁ c) (λ m → CPSVal m))
  ≡⟨ refl ⟩
    CPSLet (CPSVal (CPSFun (λ a → CPSVal (CPSFun
                           (λ κ′ →
                           CPSApp (CPSVal (CPSVar κ′))
                                  (CPSApp (CPSApp (CPSVal (CPSFun (λ x → CPSVal (CPSFun
                                                                  (λ k → cpsI′ τ₁ τ₂ τ₂
                                                                               (pcontext-plug τ₁ Hole (Val (Var x)))
                                                                               (CPSVar k))))))
                                                  (CPSVal (CPSVar a)))
                                          (CPSVal (CPSFun (λ v → κ (CPSVar v))))))))))
           (λ c → cpsI τ τ τ₃ (e₁ c) (λ m → CPSVal m))
  ≡⟨ refl ⟩
    CPSLet (CPSVal (CPSFun (λ a → CPSVal (CPSFun
                           (λ κ′ →
                           CPSApp (CPSVal (CPSVar κ′))
                                  ((λ n → CPSApp (CPSApp (CPSVal (CPSFun (λ x → CPSVal (CPSFun
                                                                          (λ k → cpsI′ τ₁ τ₂ τ₂
                                                                                        (pcontext-plug τ₁ Hole (Val (Var x))) (
                                                                                        CPSVar k))))))
<<<<<<< HEAD
                                                          (CPSVal n))
                                                  (CPSVal (CPSFun (λ v → κ (CPSVar v)))))
                                   (CPSVar a)))))))
=======
                                                          (CPSVal (CPSVar n)))
                                                  (CPSVal (CPSFun (λ v → κ (CPSVar v)))))
                                   a))))))
>>>>>>> 85b17510afd0f45f67318dad8b3c63a93f148bc5
           (λ c → cpsI τ τ τ₃ (e₁ c) (λ m → CPSVal m))
  ≡⟨ refl ⟩
    cpsI τ₁ τ₂ τ₃
         (Shift α τ τ₃ τ₁ τ₂ e₁)
         (λ n → CPSApp (CPSApp (CPSVal (CPSFun (λ x → CPSVal (CPSFun
                                                (λ k → cpsI′ τ₁ τ₂ τ₂
                                                             (pcontext-plug τ₁ Hole (Val (Var x)))
                                                             (CPSVar k))))))
                                (CPSVal n))
                        (CPSVal (CPSFun (λ v → κ (CPSVar v)))))
  ≡⟨ refl ⟩
    cpsI τ₁ τ₂ τ₃
         (Shift α τ τ₃ τ₁ τ₂ e₁)
         (λ n → CPSApp (CPSApp (CPSVal (cpsV (τ₁ ⇒ τ₁ cps[ τ₂ , τ₂ ])
                                             (Fun τ₁ τ₁ (λ x → pcontext-plug τ₁ Hole (Val (Var x))))))
                                (CPSVal n))
                        (CPSVal (CPSFun (λ v → κ (CPSVar v)))))
  ≡⟨ refl ⟩
    (λ m → cpsI τ₁ τ₂ τ₃
                 (Shift α τ τ₃ τ₁ τ₂ e₁)
                 λ n → CPSApp (CPSApp (CPSVal m) (CPSVal n))
                               (CPSVal (CPSFun (λ v → κ (CPSVar v)))))
    (cpsV (τ₁ ⇒ τ₁ cps[ τ₂ , τ₂ ])
          (Fun τ₁ τ₁ (λ x → pcontext-plug τ₁ Hole (Val (Var x)))))
  ≡⟨ refl ⟩
    cpsI (τ₁ ⇒ τ₁ cps[ τ₂ , τ₂ ]) τ₃ τ₃
         (Val (Fun τ₁ τ₁ (λ x → pcontext-plug τ₁ Hole (Val (Var x)))))
         (λ m → cpsI τ₁ τ₂ τ₃
                      (Shift α τ τ₃ τ₁ τ₂ e₁)
                      λ n → CPSApp (CPSApp (CPSVal m) (CPSVal n))
                                   (CPSVal (CPSFun λ a → κ (CPSVar a))))
  ⟵⟨ eqId ⟩
    cpsI τ₁ τ₂ τ₃
      (App (Val (Fun τ₁ τ₁ (λ x → pcontext-plug τ₁ Hole (Val (Var x)))))
<<<<<<< HEAD
           (Shift α τ τ₃ τ₁ τ₂ e₁))
      κ
  ∎

-- -- shift-lemma {τ} {τ₁} {τ₂} {τ₃} {τ₄} {τ₅} {α} {var} .(Frame {_} {τ₁} {τ₂} {τ₃} {τ₆} {τ₇} {τ₄} {τ₅} f₁ p₁) .(Frame {_} {τ₁} {τ₂} {τ₂} {τ₆} {τ₇} {τ₄} {τ₅} f₂ p₂) (Frame {τ₄ = τ₆} {τ₅ = τ₇} {τ₆ = .τ₄} {τ₇ = .τ₅} {f₁ = f₁} {f₂ = f₂} x {p₁ = p₁} {p₂ = p₂} x₁) e₁ κ sch = {!!}   

-- -- shift-lemma {τ} {τ₁} {τ₂} {τ₃} {τ₄} {τ₅} {α} {var} .(Frame {_} {τ₁} {τ₂} {τ₃} {τ₆} {τ₇} {τ₄} {τ₅} f₁ p₁′) .(Frame {_} {τ₁} {τ₂} {τ₂} {τ₆} {τ₇} {τ₄} {τ₅} f₂ p₂′) (Frame {τ₄ = τ₆} {τ₅ = τ₇} {τ₆ = .τ₄} {τ₇ = .τ₅} {f₁ = f₁} {f₂ = f₂} x {p₁ = p₁′} {p₂ = p₂′} x₁) e₁ κ sch = {!!}   

shift-lemma {τ} {τ₁} {τ₂} {τ₃} {τ₄} {τ₅} {α} {var}
            .(Frame {_} {τ₁} {τ₂} {τ₃} {τ₆ ⇒ τ₄ cps[ τ₅ , τ₈ ]} {τ₇} {τ₄} {τ₅}
              (App₁ {_} {τ₄} {τ₆} {τ₅} {τ₈} {τ₇} {τ₃} e₂) p₁′)
            .(Frame {_} {τ₁} {τ₂} {τ₂} {τ₆ ⇒ τ₄ cps[ τ₅ , τ₈ ]} {τ₇} {τ₄} {τ₅}
              (App₁ {_} {τ₄} {τ₆} {τ₅} {τ₈} {τ₇} {τ₂} e₂) p₂′)
             (Frame {τ₄ = .(τ₆ ⇒ τ₄ cps[ τ₅ , τ₈ ])} {τ₅ = τ₇} {τ₆ = .τ₄} {τ₇ = .τ₅}
               {f₁ = App₁ {τ₁ = .τ₄} {τ₂ = τ₆} {τ₃ = .τ₅} {τ₄ = τ₈} {τ₅ = .τ₇} {τ₆ = .τ₃} e₂}
               {f₂ = App₁ {τ₁ = .τ₄} {τ₂ = .τ₆} {τ₃ = .τ₅} {τ₄ = .τ₈} {τ₅ = .τ₇} {τ₆ = .τ₂} .e₂}
               (App₁ {τ₂ = .τ₆} {τ₄ = .τ₈} {τ₆ = .τ₂} .e₂) {p₁ = p₁′} {p₂ = p₂′} c)
             e₁ κ sch =
  begin
    cpsI τ₄ τ₅ τ₃
      (pcontext-plug τ₁ (Frame (App₁ e₂) p₁′) (Shift α τ τ₃ τ₁ τ₂ e₁)) κ
  ≡⟨ refl ⟩
    cpsI τ₄ τ₅ τ₃
         (pframe-plug (App₁ e₂) (pcontext-plug τ₁ p₁′ (Shift α τ τ₃ τ₁ τ₂ e₁))) κ
  ≡⟨ refl ⟩
    cpsI τ₄ τ₅ τ₃
         (App (pcontext-plug τ₁ p₁′ (Shift α τ τ₃ τ₁ τ₂ e₁)) e₂)
         κ
  ≡⟨ refl ⟩
    cpsI (τ₆ ⇒ τ₄ cps[ τ₅ , τ₈ ]) τ₇ τ₃
         (pcontext-plug τ₁ p₁′ (Shift α τ τ₃ τ₁ τ₂ e₁))
         (λ m → cpsI τ₆ τ₈ τ₇ e₂
                     (λ n → CPSApp (CPSApp (CPSVal m) (CPSVal n))
                                    (CPSVal (CPSFun (λ a → κ (CPSVar a))))))
  ⟷⟨ shift-lemma p₁′ p₂′ c e₁ (λ m → cpsI τ₆ τ₈ τ₇ e₂
                               (λ n → CPSApp (CPSApp (CPSVal m) (CPSVal n))
                                             (CPSVal (CPSFun (λ a → κ (CPSVar a))))))
                              (λ v → κSubst e₂ (λ y → λ n → CPSApp (CPSApp (CPSVal y) (CPSVal n))
                                                                     (CPSVal (CPSFun (λ v → κ (CPSVar v)))))
                                             λ x → sApp (sApp (sVal sVar=) Subst≠) Subst≠) ⟩
    cpsI (τ₆ ⇒ τ₄ cps[ τ₅ , τ₈ ]) τ₇ τ₃
         (App (Val (Fun (τ₆ ⇒ τ₄ cps[ τ₅ , τ₈ ]) τ₁
                        (λ x → pcontext-plug τ₁ p₂′ (Val (Var x)))))
                        (Shift α τ τ₃ τ₁ τ₂ e₁))
         (λ m → cpsI τ₆ τ₈ τ₇ e₂
                     (λ n → CPSApp (CPSApp (CPSVal m) (CPSVal n))
                                   (CPSVal (CPSFun (λ v → κ (CPSVar v))))))
  ≡⟨ refl ⟩
    cpsI (τ₁ ⇒ τ₆ ⇒ τ₄ cps[ τ₅ , τ₈ ] cps[ τ₇ , τ₂ ]) τ₃ τ₃
         (Val (Fun (τ₆ ⇒ τ₄ cps[ τ₅ , τ₈ ]) τ₁ (λ x → pcontext-plug τ₁ p₂′ (Val (Var x)))))
         (λ m′ → cpsI τ₁ τ₂ τ₃
                     (Shift α τ τ₃ τ₁ τ₂ e₁)
                     (λ n′ → CPSApp (CPSApp (CPSVal m′) (CPSVal n′))
                                   (CPSVal (CPSFun (λ a₁ → cpsI τ₆ τ₈ τ₇ e₂
                                                          (λ n → CPSApp (CPSApp (CPSVal (CPSVar a₁)) (CPSVal n))
                                                                        (CPSVal (CPSFun (λ v → κ (CPSVar v))))))))))
  ≡⟨ refl ⟩
    (λ m′ → cpsI τ₁ τ₂ τ₃
                (Shift α τ τ₃ τ₁ τ₂ e₁)
                (λ n′ → CPSApp (CPSApp (CPSVal m′) (CPSVal n′))
                               (CPSVal (CPSFun (λ a₁ → cpsI τ₆ τ₈ τ₇ e₂
                                                             (λ n → CPSApp (CPSApp (CPSVal (CPSVar a₁)) (CPSVal n))
                                                                           (CPSVal (CPSFun (λ v → κ (CPSVar v))))))))))
    (cpsV (τ₁ ⇒ τ₆ ⇒ τ₄ cps[ τ₅ , τ₈ ] cps[ τ₇ , τ₂ ])
          (Fun (τ₆ ⇒ τ₄ cps[ τ₅ , τ₈ ]) τ₁
          (λ x → pcontext-plug τ₁ p₂′ (Val (Var x)))))
  ≡⟨ refl ⟩
    (λ m′ → cpsI τ₁ τ₂ τ₃
                (Shift α τ τ₃ τ₁ τ₂ e₁)
                (λ n′ → CPSApp (CPSApp (CPSVal m′) (CPSVal n′))
                               (CPSVal (CPSFun (λ a₁ → cpsI τ₆ τ₈ τ₇ e₂
                                                             (λ n → CPSApp (CPSApp (CPSVal (CPSVar a₁)) (CPSVal n))
                                                                            (CPSVal (CPSFun (λ v → κ (CPSVar v))))))))))
    (CPSFun (λ x → CPSVal (CPSFun (λ k →
            cpsI′ (τ₆ ⇒ τ₄ cps[ τ₅ , τ₈ ]) τ₇ τ₂ (pcontext-plug τ₁ p₂′ (Val (Var x))) (CPSVar k)))))

  ≡⟨ refl ⟩
    cpsI τ₁ τ₂ τ₃
         (Shift α τ τ₃ τ₁ τ₂ e₁)
         (λ n′ → CPSApp (CPSApp (CPSVal (CPSFun (λ x → CPSVal (CPSFun (λ k →
                                                cpsI′ (τ₆ ⇒ τ₄ cps[ τ₅ , τ₈ ]) τ₇ τ₂
                                                      (pcontext-plug τ₁ p₂′ (Val (Var x))) (CPSVar k))))))
                                (CPSVal n′))
                        (CPSVal (CPSFun (λ a₁ → cpsI τ₆ τ₈ τ₇ e₂
                                                     (λ n → CPSApp (CPSApp (CPSVal (CPSVar a₁)) (CPSVal n))
                                                                   (CPSVal (CPSFun (λ v → κ (CPSVar v)))))))))
  ≡⟨ refl ⟩
    CPSLet (CPSVal (CPSFun λ a → CPSVal (CPSFun (λ κ′ →
           CPSApp (CPSVal (CPSVar κ′))
                  (CPSApp (CPSApp (CPSVal (CPSFun (λ x → CPSVal (CPSFun (λ k →
                                          cpsI′ (τ₆ ⇒ τ₄ cps[ τ₅ , τ₈ ]) τ₇ τ₂
                                                (pcontext-plug τ₁ p₂′ (Val (Var x))) (CPSVar k))))))
                                  (CPSVal (CPSVar a)))
                          (CPSVal (CPSFun (λ a₁ → cpsI τ₆ τ₈ τ₇ e₂
                                          (λ n → CPSApp (CPSApp (CPSVal (CPSVar a₁)) (CPSVal n))
                                                         (CPSVal (CPSFun (λ v → κ (CPSVar v)))))))))))))
           (λ c → cpsI τ τ τ₃ (e₁ c) (λ m → CPSVal m))
  ⟶⟨ eqLet₁ (λ c → cpsI τ τ τ₃ (e₁ c) (λ m → CPSVal m))
              (eqFun (λ a → eqFun (λ κ′ → eqApp₂ (eqApp₁ (eqBeta (sVal (sFun (λ k →
              ekSubst′ {e₁ = λ x → pcontext-plug τ₁ p₂′ (Val (Var x))} {e₂ = pcontext-plug τ₁ p₂′ (Val (Var a))}
                       k (subst-context p₂′ (Var a)))))))))) ⟩
    CPSLet (CPSVal (CPSFun λ a → CPSVal (CPSFun (λ κ′ →
           CPSApp (CPSVal (CPSVar κ′))
                  (CPSApp (CPSVal (CPSFun (λ k → cpsI′ (τ₆ ⇒ τ₄ cps[ τ₅ , τ₈ ]) τ₇ τ₂
                                                 (pcontext-plug τ₁ p₂′ (Val (Var a))) (CPSVar k))))
                          (CPSVal (CPSFun (λ a₁ → cpsI τ₆ τ₈ τ₇ e₂
                                          (λ n → CPSApp (CPSApp (CPSVal (CPSVar a₁)) (CPSVal n))
                                                         (CPSVal (CPSFun (λ v → κ (CPSVar v)))))))))))))
           (λ c → cpsI τ τ τ₃ (e₁ c) (λ m → CPSVal m))
  ⟶⟨ eqLet₁ (λ c → cpsI τ τ τ₃ (e₁ c) (λ m → CPSVal m))
               (eqFun (λ a → eqFun (λ κ′ → eqApp₂ (eqBeta (kSubst′ (pcontext-plug τ₁ p₂′ (Val (Var a)))))))) ⟩
    CPSLet (CPSVal (CPSFun λ a → CPSVal (CPSFun (λ κ′ →
           CPSApp (CPSVal (CPSVar κ′))
                  (cpsI′ (τ₆ ⇒ τ₄ cps[ τ₅ , τ₈ ]) τ₇ τ₂ (pcontext-plug τ₁ p₂′ (Val (Var a)))
                  (CPSFun (λ a₁ → cpsI τ₆ τ₈ τ₇ e₂
                                       (λ n → CPSApp (CPSApp (CPSVal (CPSVar a₁)) (CPSVal n))
                                                     (CPSVal (CPSFun (λ v → κ (CPSVar v))))))))))))
           (λ c → cpsI τ τ τ₃ (e₁ c) (λ m → CPSVal m))
  ≡⟨ refl ⟩
    CPSLet (CPSVal (CPSFun λ a → CPSVal (CPSFun (λ κ′ →
           CPSApp (CPSVal (CPSVar κ′))
                  (cpsI′ (τ₆ ⇒ τ₄ cps[ τ₅ , τ₈ ]) τ₇ τ₂ (pcontext-plug τ₁ p₂′ (Val (Var a)))
                  (CPSFun (λ a₁ → (λ y → cpsI τ₆ τ₈ τ₇ e₂
                                               (λ n → CPSApp (CPSApp (CPSVal y) (CPSVal n))
                                                              (CPSVal (CPSFun (λ v → κ  (CPSVar v))))))
                                   (CPSVar a₁))))))))
           (λ c → cpsI τ τ τ₃ (e₁ c) (λ m → CPSVal m))
  ⟶⟨ eqLet₁ (λ c → cpsI τ τ τ₃ (e₁ c) (λ m → CPSVal m))
              (eqFun (λ a → eqFun (λ κ′ → eqApp₂
              (cpsEtaEta′ (pcontext-plug τ₁ p₂′ (Val (Var a)))
                          (λ y → cpsI τ₆ τ₈ τ₇ e₂
                                 (λ n → CPSApp (CPSApp (CPSVal y) (CPSVal n))
                                               (CPSVal (CPSFun (λ v → κ (CPSVar v))))))
                          λ v′ → κSubst e₂ (λ y → λ n → CPSApp (CPSApp (CPSVal y) (CPSVal n))
                                                                  (CPSVal (CPSFun (λ v → κ (CPSVar v)))))
                                        λ v′′ → sApp (sApp (sVal sVar=) Subst≠) (sVal (sFun (λ v → Subst≠))))))) ⟩
    CPSLet (CPSVal (CPSFun λ a → CPSVal (CPSFun (λ κ′ →
           CPSApp (CPSVal (CPSVar κ′))
                  (cpsI (τ₆ ⇒ τ₄ cps[ τ₅ , τ₈ ]) τ₇ τ₂ (pcontext-plug τ₁ p₂′ (Val (Var a)))
                        (λ y → cpsI τ₆ τ₈ τ₇ e₂
                                    (λ n → CPSApp (CPSApp (CPSVal y) (CPSVal n))
                                                   (CPSVal (CPSFun (λ v → κ (CPSVar v)))))))))))
           (λ c → cpsI τ τ τ₃ (e₁ c) (λ m → CPSVal m))
  ⟵⟨ {!!} ⟩
    CPSLet (CPSVal (CPSFun (λ a → CPSVal (CPSFun (λ κ′ →
                     CPSApp (CPSVal (CPSVar κ′))
                            (CPSApp (CPSVal (CPSFun (λ k → cpsI (τ₆ ⇒ τ₄ cps[ τ₅ , τ₈ ]) τ₇ τ₂
                                                                (pcontext-plug τ₁ p₂′ (Val (Var a)))
                                                                (λ m₁ → cpsI τ₆ τ₈ τ₇ e₂
                                                                         λ n₁ → CPSApp (CPSApp (CPSVal m₁) (CPSVal n₁))
                                                                                       (CPSVal (CPSVar k))))))
                                    (CPSVal (CPSFun (λ v → κ (CPSVar v))))))))))
           (λ c → cpsI τ τ τ₃ (e₁ c) (λ m → CPSVal m))
  ⟵⟨ eqLet₁ (λ c → cpsI τ τ τ₃ (e₁ c) (λ m → CPSVal m))
             (eqFun (λ a → eqFun (λ κ′ → eqApp₂ (eqApp₁ (eqBeta (sVal (sFun λ k →
             eSubst {e₁ = (λ x → pcontext-plug τ₁ p₂′ (Val (Var x)))} {e₂ = pcontext-plug τ₁ p₂′ (Val (Var a))}
                    {v = Var a}
                    (subst-context p₂′ (Var a))
                    λ sub → κSubst e₂ (λ v′ → λ n₁ → CPSApp (CPSApp (CPSVal {!v₁′!}) (CPSVal n₁)) (CPSVal (CPSVar k)))
                                    {!!})
                     )))))) ⟩
    CPSLet (CPSVal (CPSFun (λ a → CPSVal (CPSFun (λ κ′ →
                     CPSApp (CPSVal (CPSVar κ′))
                            (CPSApp (CPSApp (CPSVal (CPSFun (λ x → CPSVal (CPSFun (λ k →
                                                    cpsI (τ₆ ⇒ τ₄ cps[ τ₅ , τ₈ ]) τ₇ τ₂
                                                         (pcontext-plug τ₁ p₂′ (Val (Var x)))
                                                         (λ m₁ → cpsI τ₆ τ₈ τ₇ e₂
                                                                 (λ n₁ → CPSApp (CPSApp (CPSVal m₁) (CPSVal n₁))
                                                                                (CPSVal (CPSVar k)))))))))
                                            (CPSVal (CPSVar a)))
                                    (CPSVal (CPSFun (λ v → κ (CPSVar v))))))))))
           (λ c → cpsI τ τ τ₃ (e₁ c) (λ m → CPSVal m))
  ≡⟨ refl ⟩
    cpsI τ₁ τ₂ τ₃
         (Shift α τ τ₃ τ₁ τ₂ e₁)
         (λ n → CPSApp (CPSApp (CPSVal (CPSFun (λ x → CPSVal (CPSFun (λ k →
                                       cpsI (τ₆ ⇒ τ₄ cps[ τ₅ , τ₈ ]) τ₇ τ₂ (pcontext-plug τ₁ p₂′ (Val (Var x)))
                                            (λ m₁ → cpsI τ₆ τ₈ τ₇ e₂
                                                    (λ n₁ → CPSApp (CPSApp (CPSVal m₁) (CPSVal n₁)) (CPSVal (CPSVar k)))))))))
                                (CPSVal n))
                        (CPSVal (CPSFun (λ v → κ (CPSVar v)))))
  ≡⟨ refl ⟩
    (λ m → cpsI τ₁ τ₂ τ₃
                 (Shift α τ τ₃ τ₁ τ₂ e₁)
                 (λ n → CPSApp (CPSApp (CPSVal m) (CPSVal n))
                                (CPSVal (CPSFun (λ v → κ (CPSVar v))))))
    (CPSFun (λ x → CPSVal (CPSFun (λ k →
    cpsI (τ₆ ⇒ τ₄ cps[ τ₅ , τ₈ ]) τ₇ τ₂ (pcontext-plug τ₁ p₂′ (Val (Var x)))
         (λ m₁ → cpsI τ₆ τ₈ τ₇ e₂
         (λ n₁ → CPSApp (CPSApp (CPSVal m₁) (CPSVal n₁)) (CPSVal (CPSVar k))))))))
  ≡⟨ refl ⟩
    (λ m → cpsI τ₁ τ₂ τ₃
                 (Shift α τ τ₃ τ₁ τ₂ e₁)
                 (λ n → CPSApp (CPSApp (CPSVal m) (CPSVal n))
                                (CPSVal (CPSFun (λ v → κ (CPSVar v))))))
    (CPSFun (λ x → CPSVal (CPSFun (λ k →
    cpsI′ τ₄ τ₅ τ₂ (App (pcontext-plug τ₁ p₂′ (Val (Var x))) e₂) (CPSVar k)))))
  ≡⟨ refl ⟩
    (λ m → cpsI τ₁ τ₂ τ₃
                 (Shift α τ τ₃ τ₁ τ₂ e₁)
                 (λ n → CPSApp (CPSApp (CPSVal m) (CPSVal n))
                                (CPSVal (CPSFun (λ v → κ (CPSVar v))))))
    (CPSFun (λ x → CPSVal (CPSFun (λ k →
    cpsI′ τ₄ τ₅ τ₂ (pframe-plug (App₁ e₂) (pcontext-plug τ₁ p₂′ (Val (Var x)))) (CPSVar k)))))
  ≡⟨ refl ⟩
    (λ m → cpsI τ₁ τ₂ τ₃
                 (Shift α τ τ₃ τ₁ τ₂ e₁)
                 (λ n → CPSApp (CPSApp (CPSVal m) (CPSVal n))
                                (CPSVal (CPSFun (λ v → κ (CPSVar v))))))
    (CPSFun (λ x → CPSVal (CPSFun (λ k →
    cpsI′ τ₄ τ₅ τ₂ (pcontext-plug τ₁ (Frame (App₁ e₂) p₂′) (Val (Var x))) (CPSVar k)))))
  ≡⟨ refl ⟩
    (λ m → cpsI τ₁ τ₂ τ₃
                 (Shift α τ τ₃ τ₁ τ₂ e₁)
                 (λ n → CPSApp (CPSApp (CPSVal m) (CPSVal n))
                                (CPSVal (CPSFun (λ v → κ (CPSVar v))))))
    (cpsV (τ₁ ⇒ τ₄ cps[ τ₅ , τ₂ ]) (Fun τ₄ τ₁ λ x → pcontext-plug τ₁ (Frame (App₁ e₂) p₂′) (Val (Var x))))
  ≡⟨ refl ⟩
    cpsI (τ₁ ⇒ τ₄ cps[ τ₅ , τ₂ ]) τ₃ τ₃
         (Val (Fun τ₄ τ₁ (λ x → pcontext-plug τ₁ (Frame (App₁ e₂) p₂′) (Val (Var x)))))
         (λ m → cpsI τ₁ τ₂ τ₃
                     (Shift α τ τ₃ τ₁ τ₂ e₁)
                     (λ n → CPSApp (CPSApp (CPSVal m) (CPSVal n))
                                    (CPSVal (CPSFun (λ v → κ (CPSVar v))))))
  ≡⟨ refl ⟩
    cpsI τ₄ τ₅ τ₃ (App (Val (Fun τ₄ τ₁ (λ x → pcontext-plug τ₁ (Frame (App₁ e₂) p₂′) (Val (Var x)))))
         (Shift α τ τ₃ τ₁ τ₂ e₁))
         κ
  ∎

shift-lemma {τ} {τ₁} {τ₂} {τ₃} {τ₄} {τ₅} {α} {var}
           .(Frame {_} {τ₁} {τ₂} {τ₃} {τ₆} {τ₇} {τ₄} {τ₅} (App₂ {_} {τ₄} {τ₆} {τ₅} {τ₇} {τ₃} v₁) p₁)
           .(Frame {_} {τ₁} {τ₂} {τ₂} {τ₆} {τ₇} {τ₄} {τ₅} (App₂ {_} {τ₄} {τ₆} {τ₅} {τ₇} {τ₂} v₂) p₂)
            (Frame {τ₄ = τ₆} {τ₅ = τ₇} {τ₆ = .τ₄} {τ₇ = .τ₅}
                   {f₁ = App₂ {τ₁ = .τ₄} {τ₂ = .τ₆} {τ₃ = .τ₅} {τ₄ = .τ₇} {τ₅ = .τ₃} v₁}
                   {f₂ = App₂ {τ₁ = .τ₄} {τ₂ = .τ₆} {τ₃ = .τ₅} {τ₄ = .τ₇} {τ₅ = .τ₂} v₂} x {p₁ = p₁} {p₂ = p₂} c)
            e₁ κ sch = {!!} 
            
=======
       (Shift α τ τ₃ τ₁ τ₂ e₁))
      κ
  ∎
  
shift-lemma {τ} {τ₁} {τ₂} {τ₃} {τ₄} {τ₅} {α} {var}
  .(Frame {_} {τ₁} {τ₂} {τ₃} {τ₆} {τ₇} {τ₄} {τ₅} f₁ p₁)
  .(Frame {_} {τ₁} {τ₂} {τ₂} {τ₆} {τ₇} {τ₄} {τ₅} f₂ p₂)
  (Frame {τ₄ = τ₆} {τ₅ = τ₇} {τ₆ = .τ₄} {τ₇ = .τ₅} {f₁ = f₁} {f₂ = f₂} x {p₁ = p₁} {p₂ = p₂} x₁)
  e₁ κ sch = {!!}                                            
>>>>>>> 85b17510afd0f45f67318dad8b3c63a93f148bc5

               

{----------------Term Definition----------------}

correctII : {var : cpstyp → Set} → {τ₁ τ₂ τ₃ : typ} →
            {e  : term[ var ∘ cpsT ] τ₁ cps[ τ₂ , τ₃ ]} →
            {e′ : term[ var ∘ cpsT ] τ₁ cps[ τ₂ , τ₃ ]} →
            (κ : cpsvalue[ var ] (cpsT τ₁) → cpsterm[ var ] (cpsT τ₂)) →
            schematicV {var} {τ₁} {τ₂} κ →
            Reduce e e′ →
            cpsequal (cpsI τ₁ τ₂ τ₃ e κ) (cpsI τ₁ τ₂ τ₃ e′ κ)

correctII {τ₁ = τ₁} {τ₂} {τ₃} {e′ = e₂} κ sche (RBeta {τ} {e₁ = e₁} {v₂} {e₁′ = e₂} sub) =
  begin
    cpsI τ₁ τ₂ τ₃ (App (Val (Fun τ₁ τ e₁)) (Val v₂)) κ
  ≡⟨ refl ⟩
    CPSApp (CPSApp (CPSVal (CPSFun (λ x → CPSVal (CPSFun λ k → cpsI′ τ₁ τ₂ τ₃ (e₁ x) (CPSVar k)))))
                   (CPSVal (cpsV τ v₂)))
           (CPSVal (CPSFun (λ a → κ (CPSVar a))))
  ⟶⟨ eqApp₁ (eqBeta (sVal (sFun (λ k → ekSubst′ k sub)))) ⟩ 
    CPSApp (CPSVal (CPSFun (λ k → cpsI′ τ₁ τ₂ τ₃ e₂ (CPSVar k))))
           (CPSVal (CPSFun (λ a → κ (CPSVar a))))
  ⟶⟨ eqBeta (kSubst′ e₂) ⟩
    cpsI′ τ₁ τ₂ τ₃ e₂ (CPSFun (λ a → κ (CPSVar a)))
  ⟶⟨ cpsEtaEta′ e₂ κ sche ⟩
    cpsI τ₁ τ₂ τ₃ e₂ κ
  ∎

correctII {τ₁ = τ₁} {τ₂} {τ₃} κ sche
          (RFrame {τ₁ = .(τ₅ ⇒ τ₁ cps[ τ₂ , τ₆ ])} {τ₂ = τ₄} {τ₃ = .τ₃} {τ₄ = .τ₁} {τ₅ = .τ₂} {τ₆ = .τ₃}
          {e₁ = e₁} {e₂ = e₁′}
          (App₁ {τ₁ = .τ₁} {τ₂ = τ₅} {τ₃ = .τ₂} {τ₄ = τ₆} {τ₅ = .τ₄} {τ₆ = .τ₃} e₂) sub) =
  begin
    cpsI τ₁ τ₂ τ₃ (App e₁ e₂) κ
  ≡⟨ refl ⟩
    cpsI (τ₅ ⇒ τ₁ cps[ τ₂ , τ₆ ]) τ₄ τ₃ e₁
         (λ m → cpsI τ₅ τ₆ τ₄ e₂
         (λ n → CPSApp (CPSApp (CPSVal m) (CPSVal n)) (CPSVal (CPSFun (λ a → κ (CPSVar a))))))
  ⟶⟨ correctII (λ m → cpsI τ₅ τ₆ τ₄ e₂
                        (λ n → CPSApp (CPSApp (CPSVal m) (CPSVal n))
                                      (CPSVal (CPSFun (λ a → κ (CPSVar a))))))
                 (λ v → κSubst e₂ (λ m →
                                   (λ n → CPSApp (CPSApp (CPSVal m) (CPSVal n))
                                                  (CPSVal (CPSFun (λ a → κ (CPSVar a))))))
                                   λ k₁ → sApp (sApp (sVal sVar=) (sVal SubstV≠))
                                                (sVal (sFun (λ k₂ → Subst≠))))
                 sub ⟩
    cpsI (τ₅ ⇒ τ₁ cps[ τ₂ , τ₆ ]) τ₄ τ₃ e₁′
         (λ m → cpsI τ₅ τ₆ τ₄ e₂
         (λ n → CPSApp (CPSApp (CPSVal m) (CPSVal n))
                        (CPSVal (CPSFun (λ a → κ (CPSVar a))))))
  ⟶⟨ eqId ⟩
    cpsI τ₁ τ₂ τ₃ (App e₁′ e₂) κ
  ∎

correctII {τ₁ = τ₁} {τ₂} {τ₃} κ sche
          (RFrame {τ₁ = τ₄} {τ₂ = τ₅} {τ₃ = .τ₃} {τ₄ = .τ₁} {τ₅ = .τ₂} {τ₆ = .τ₃} {e₁ = e₂} {e₂ = e₂′}
          (App₂ {τ₁ = .τ₁} {τ₂ = .τ₄} {τ₃ = .τ₂} {τ₄ = .τ₅} {τ₅ = .τ₃} v₁) sub) =
  begin
    cpsI τ₁ τ₂ τ₃ (App (Val v₁) e₂) κ
  ≡⟨ refl ⟩
    cpsI (τ₄ ⇒ τ₁ cps[ τ₂ , τ₅ ]) τ₃ τ₃ (Val v₁)
    (λ m → cpsI τ₄ τ₅ τ₃ e₂
           (λ n → CPSApp (CPSApp (CPSVal m) (CPSVal n)) (CPSVal (CPSFun (λ a → κ (CPSVar a))))))
  ≡⟨ refl ⟩
    cpsI τ₄ τ₅ τ₃ e₂
    (λ n → CPSApp (CPSApp (CPSVal (cpsV (τ₄ ⇒ τ₁ cps[ τ₂ , τ₅ ]) v₁)) (CPSVal n))
                           (CPSVal (CPSFun (λ a → κ (CPSVar a)))))
  ⟶⟨ correctII (λ n → CPSApp (CPSApp (CPSVal (cpsV (τ₄ ⇒ τ₁ cps[ τ₂ , τ₅ ]) v₁)) (CPSVal n))
                               (CPSVal (CPSFun (λ a → κ (CPSVar a)))))
                (λ v → sApp (sApp (sVal SubstV≠) (sVal sVar=))
                             (sVal (sFun (λ a → Subst≠))))
                sub ⟩
    cpsI τ₄ τ₅ τ₃ e₂′
      (λ n′ → CPSApp (CPSApp (CPSVal (cpsV (τ₄ ⇒ τ₁ cps[ τ₂ , τ₅ ]) v₁)) (CPSVal n′))
                     (CPSVal (CPSFun (λ a → κ (CPSVar a)))))
  ⟶⟨ eqId ⟩
    cpsI τ₁ τ₂ τ₃ (App (Val v₁) e₂′) κ
  ∎

correctII {τ₁ = τ₁} {τ₂} {.τ₂} κ sche
          (RFrame {τ₁ = τ₃} {τ₂ = .τ₃} {τ₃ = .τ₁} {τ₄ = .τ₁} {τ₅ = .τ₂} {τ₆ = .τ₂} {e₁ = e} {e₂ = e′}
          (Reset {τ₁ = .τ₃} {τ₂ = .τ₁} {τ₃ = .τ₂}) sub) =
  begin
    cpsI τ₁ τ₂ τ₂ (Reset τ₃ τ₁ τ₂ e) κ
  ≡⟨ refl ⟩
    CPSLet (cpsI τ₃ τ₃ τ₁ e (λ m → CPSVal m))
           (λ c → κ (CPSVar c))
  ⟶⟨ eqLet₁ (λ c → κ (CPSVar c))
              (correctII (λ m → CPSVal m) (λ v → sVal sVar=) sub) ⟩
    CPSLet (cpsI τ₃ τ₃ τ₁ e′ CPSVal) (λ c → κ (CPSVar c))
  ⟶⟨ eqId ⟩
    cpsI τ₁ τ₂ τ₂ (Reset τ₃ τ₁ τ₂ e′) κ
  ∎

correctII {τ₁ = τ₁} {τ₂} {.τ₂} κ sche
          (RReset {τ₁ = .τ₁} {τ₂ = .τ₂} {v₁ = v}) =
  begin
    cpsI τ₁ τ₂ τ₂ (Reset τ₁ τ₁ τ₂ (Val v)) κ
  ≡⟨ refl ⟩
    CPSLet (cpsI τ₁ τ₁ τ₁ (Val v) (λ m → CPSVal m))
           (λ c → κ (CPSVar c))
  ≡⟨ refl ⟩
    CPSLet (CPSVal (cpsV τ₁ v)) (λ c → κ (CPSVar c))
  ⟶⟨ eqLet (sche v) ⟩
    κ (cpsV τ₁ v)
  ⟶⟨ eqId ⟩
    cpsI τ₁ τ₂ τ₂ (Val v) κ
  ∎

correctII {var} {τ₁} {τ₂} {.τ₂}
          {.(Reset τ₄ τ₁ τ₂ (pcontext-plug {λ x → var (cpsT x)} {τ₄} τ₀ {τ₄} {τ} {τ₁} p₁ (Shift α τ₃ τ₁ τ₀ τ e₁)))}
          {.(Reset τ₃ τ₁ τ₂ (App {_} {τ₃} {τ₀ ⇒ τ cps[ α , α ]} {τ₃} {τ₁} {τ₁} {τ₁}
                   (Val {_} {(τ₀ ⇒ τ cps[ α , α ]) ⇒ τ₃ cps[ τ₃ , τ₁ ]} {τ₁}
                     (Fun τ₃ (τ₀ ⇒ τ cps[ α , α ]) {τ₃} {τ₁} e₁))
                   (Val {_} {τ₀ ⇒ τ cps[ α , α ]} {τ₁}
                     (Fun τ τ₀ {α} {α}
                       (λ x → Reset τ₄ τ α (pcontext-plug {λ x₁ → var (cpsT x₁)} {τ₄} τ₀ {τ₄} {τ} {τ} p₂
                         (Val {_} {τ₀} {τ} (Var {_} {τ₀} x))))))))}
          κ sche
          (RShift {τ₀ = τ₀} {τ₁ = τ₃} {τ₂ = .τ₁} {τ₃ = .τ₂} {τ₄ = τ₄} {τ = τ} {α = α} p₁ p₂ e₁) =
  begin
    cpsI τ₁ τ₂ τ₂ (Reset τ₄ τ₁ τ₂
                        (pcontext-plug τ₀ p₁ (Shift α τ₃ τ₁ τ₀ τ e₁))) κ
  ≡⟨ refl ⟩
    CPSLet
      (cpsI τ₄ τ₄ τ₁ (pcontext-plug τ₀ p₁ (Shift α τ₃ τ₁ τ₀ τ e₁))
       CPSVal)
      (λ c → κ (CPSVar c))
  ⟶⟨ {!!} ⟩
    {!!}
  ⟶⟨ {!!} ⟩
    cpsI τ₁ τ₂ τ₂
      (Reset τ₃ τ₁ τ₂
       (App (Val (Fun τ₃ (τ₀ ⇒ τ cps[ α , α ]) e₁))
        (Val
         (Fun τ τ₀
          (λ x → Reset τ₄ τ α (pcontext-plug τ₀ p₂ (Val (Var x))))))))
      κ
  ∎
    


