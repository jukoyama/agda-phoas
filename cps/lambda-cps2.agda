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
  cpsI τ₁ τ₂ .τ₂ (Reset τ₃ .τ₁ .τ₂ e₁) κ = CPSLet (cpsI τ₃ τ₃ τ₁ e₁ CPSVal) (λ v → κ (CPSVar v))
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
    CPSApp (CPSVal k) (cpsI τ₃ τ₃ τ₁ e₁ CPSVal) 
    -- CPSLet (cpsI τ₃ τ₃ τ₁ e₁ CPSVal) (λ a → CPSApp (CPSVal k) (CPSVal (CPSVar a)))
  cpsI′ τ₁ τ₂ τ₃  (Shift τ τ₄ .τ₃ .τ₁ .τ₂ e) k = {!!}
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
  SubstV≠ {t = CPSNum n} = sNum
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
  eSubstV {var} {τ₁} {τ = τ₂} {v₁} {v₁′} {v} (sFun sub) = {!!}
    -- sFun (λ x → sVal (sFun (λ k → ekSubst′ {!!} (sub x))))

  -- ([e₁]′ @ k)[v/y] = [e₂]′ @ k
  ekSubst′ : {var : cpstyp → Set} {τ₁ τ₂ τ₃ τ : typ} →
             {e₁ : var (cpsT τ) →
                   term[ var ∘ cpsT ] τ₁ cps[ τ₂ , τ₃ ]} →
             (e₂ : term[ var ∘ cpsT ] τ₁ cps[ τ₂ , τ₃ ]) →
             {v  : value[ var ∘ cpsT ] τ cps[τ,τ]} →
             (k  : cpsvalue[ var ] (cpsT τ₁ ⇒ cpsT τ₂)) →
             -- (k  : var (cpsT τ₁ ⇒ cpsT τ₂)) →
             Subst e₁ v e₂ →
             -- cpsSubst (λ x′ → cpsI′ τ₁ τ₂ τ₃ {var = var} (e₁ x′) (CPSVar k))
             --          (cpsV τ v)
             --          (cpsI′ τ₁ τ₂ τ₃ e₂ (CPSVar k))
             cpsSubst (λ x′ → cpsI′ τ₁ τ₂ τ₃ {var = var} (e₁ x′) k)
                      (cpsV τ v)
                      (cpsI′ τ₁ τ₂ τ₃ e₂ k)
  ekSubst′ (Val x) k (sVal sVar=) = sApp (sVal SubstV≠) (sVal cpsSubstVal.sVar=)
  ekSubst′ (Val y) k (sVal sVar≠) = {!!}
  ekSubst′ (Val .(Num _)) k (sVal sNum) = {!!}
  ekSubst′ (Val .(Fun _ _ _)) k (sVal (sFun x)) = {!!}
  ekSubst′ (App e₂ e₃) k x = {!!}
  ekSubst′ (Reset τ₁ τ₂ τ₃ e₂) k x = {!!}
  ekSubst′ (Shift τ τ₁ τ₂ τ₃ τ₄ x₁) k x = {!!}
  -- ekSubst′ {e₁ = .(λ x → Val (_ x))}             k (sVal sub)      =
  --   sApp (sVal cpsSubstVal.sVar≠) (sVal (eSubstV sub))
  -- ekSubst′ {e₁ = .(λ y → App (_ y) (_ y))}       k (sApp sub sub₁) =
  --   {!!}
  -- ekSubst′ {e₁ = .(λ y → Shift _ _ _ _ _ (_ y))} k (sShift x) = {!!}
  -- ekSubst′ {e₁ = .(λ y → Reset _ _ _ (_ y))}     k (sReset x) = {!!}

-- k[v/k] = v ⟶ [e]′@(k[v/k]) = [e′]′@(k[v/k]) = [e′]′@v
kSubst′ : {var : cpstyp → Set} {τ₁ τ₂ τ₃ : typ} {τ : cpstyp} →
          (e : term[ var ∘ cpsT ] τ₁ cps[ τ₂ , τ₃ ]) →
          {v : cpsvalue[ var ] (cpsT τ₁ ⇒ cpsT τ₂)} →
          cpsSubst (λ k → cpsI′ τ₁ τ₂ τ₃ e (CPSVar k)) v (cpsI′ τ₁ τ₂ τ₃ e v)
kSubst′ = {!!}


{----------------SCHEMATIC----------------}

schematic : {var : cpstyp → Set} {τ₁ τ₂ : typ} →
            (κ : cpsvalue[ var ] (cpsT τ₁) →
                  cpsterm[ var ] (cpsT τ₂)) → Set
schematic {var} {τ₁} {τ₂} κ =
  (v : value[ var ∘ cpsT ] τ₁ cps[τ,τ]) →
  cpsSubst (λ y → κ (CPSVar y)) (cpsV τ₁ v) (κ (cpsV τ₁ v))

-- @ [e]′ (λv.@'κ v) ⟶* @' [e] κ
cpsEtaEta′ : {var : cpstyp → Set} → {τ₁ τ₂ τ₃ : typ} →
             {e   : term[ var ∘ cpsT ] τ₁ cps[ τ₂ , τ₃ ]} →
             (κ  : cpsvalue[ var ] (cpsT τ₁) → cpsterm[ var ] (cpsT τ₂)) →
             cpsequal (cpsI′ τ₁ τ₂ τ₃ e (CPSFun (λ a → κ (CPSVar a)))) (cpsI τ₁ τ₂ τ₃ e κ)
cpsEtaEta′ = {!!}

{----------------Term Definition----------------}

correctII : {var : cpstyp → Set} → {τ₁ τ₂ τ₃ : typ} →
            {e  : term[ var ∘ cpsT ] τ₁ cps[ τ₂ , τ₃ ]} →
            {e′ : term[ var ∘ cpsT ] τ₁ cps[ τ₂ , τ₃ ]} →
            (κ : cpsvalue[ var ] (cpsT τ₁) → cpsterm[ var ] (cpsT τ₂)) →
            schematic {var} {τ₁} {τ₂} κ →
            Reduce e e′ →
            cpsequal (cpsI τ₁ τ₂ τ₃ e κ) (cpsI τ₁ τ₂ τ₃ e′ κ)

correctII = {!!}
