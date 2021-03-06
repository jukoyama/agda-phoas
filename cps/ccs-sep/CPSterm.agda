module CPSterm where

open import DSterm

open import Data.Unit
open import Data.Empty
open import Data.Nat
open import Data.Product
open import Function
open import Relation.Binary.PropositionalEquality

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
    CPSShift : {τ₁ τ₂ τ₃ τ₄ τ₅ : cpstyp} →
               cpsvalue[ var ]
                 (((τ₁ ⇒ ((τ₂ ⇒ τ₃) ⇒ τ₃)) ⇒ ((τ₄ ⇒ τ₄) ⇒ τ₅)) ⇒ ((τ₁ ⇒ τ₂) ⇒ τ₅))

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
  cpsV .(((τ₃ ⇒ τ₄ cps[ τ , τ ]) ⇒ τ₁ cps[ τ₁ , τ₂ ]) ⇒ τ₃ cps[ τ₄ , τ₂ ]) {var}
       (Shift {τ = τ} {τ₁ = τ₁} {τ₂ = τ₂} {τ₃ = τ₃} {τ₄ = τ₄}) =
       CPSFun (λ w → CPSVal (CPSFun (λ k →
                 CPSApp
                   (CPSApp (CPSVal (CPSVar w))
                           (CPSVal (CPSFun
                             (λ a → CPSVal (CPSFun (λ k′ →
                               CPSApp (CPSVal (CPSVar k′))
                                      (CPSApp (CPSVal (CPSVar k)) (CPSVal (CPSVar a)))))))))
                       (CPSVal (CPSFun (λ m → CPSVal (CPSVar m)))))))

  cpsI : (τ₁ τ₂ τ₃ : typ) → {var : cpstyp → Set} →
         term[ var ∘ cpsT ] τ₁ cps[ τ₂ , τ₃ ] →
         (cpsvalue[ var ] (cpsT τ₁) → cpsterm[ var ] (cpsT τ₂)) → 
         cpsterm[ var ] (cpsT τ₃)
         
  cpsI τ₁ τ₂ .τ₂ (Val v) κ = κ (cpsV τ₁ v)
  cpsI τ₁ τ₂ τ₃  (NonVal (App {τ₂ = τ₄} {τ₄ = τ₅} {τ₆} e₁ e₂)) κ =
    cpsI (τ₄ ⇒ τ₁ cps[ τ₂ , τ₅ ]) τ₆ τ₃
         e₁
         (λ m → cpsI τ₄ τ₅ τ₆
                      e₂
                      (λ n → CPSApp (CPSApp (CPSVal m) (CPSVal n))
                                     (CPSVal (CPSFun (λ a → κ (CPSVar a))))))
                                     -- λκ.(@κ (@ [M] (λm.m)))
  cpsI τ₁ τ₂ .τ₂ (NonVal (Reset τ₃ .τ₁ .τ₂ e₁)) κ =
    CPSApp (CPSVal (CPSFun (λ x → κ (CPSVar x)))) (cpsI τ₃ τ₃ τ₁ e₁ (λ m → CPSVal m))
    -- CPSLet (cpsI τ₃ τ₃ τ₁ e₁ (λ m → CPSVal m)) (λ v → κ (CPSVar v))
  cpsI τ₁ τ₂ τ₃  (NonVal (Let {τ₁ = τ₄} {τ₂ = .τ₁} {α = .τ₂} {β = β} {γ = .τ₃} e₁ e₂)) κ =
    -- cpsI τ₄ β τ₃ e₁
    --      (λ n → CPSLet (CPSVal n) (λ x′ → cpsI τ₁ τ₂ β (e₂ x′) κ))
    cpsI τ₄ β τ₃ e₁
         (λ m → CPSApp (CPSVal (CPSFun (λ c → cpsI τ₁ τ₂ β (e₂ c) κ))) (CPSVal m))

  cpsI′ : (τ₁ τ₂ τ₃ : typ) → {var : cpstyp → Set} →
          term[ var ∘ cpsT ] τ₁ cps[ τ₂ , τ₃ ] →
          cpsvalue[ var ] (cpsT τ₁ ⇒ cpsT τ₂) →
          cpsterm[ var ] (cpsT τ₃)
  cpsI′ τ₁ τ₂ .τ₂ (Val v) k = CPSApp (CPSVal k) (CPSVal (cpsV τ₁ v))
  cpsI′ τ₁ τ₂ τ₃  (NonVal (App {τ₂ = τ₄} {τ₄ = τ₅} {τ₆} e₁ e₂)) k =
    cpsI (τ₄ ⇒ τ₁ cps[ τ₂ , τ₅ ]) τ₆ τ₃
         e₁ (λ m → cpsI τ₄ τ₅ τ₆ e₂ (λ n → CPSApp (CPSApp (CPSVal m) (CPSVal n)) (CPSVal k)))
  cpsI′ τ₁ τ₂ .τ₂ (NonVal (Reset τ₃ .τ₁ .τ₂ e₁)) k =
    CPSApp (CPSVal k) (cpsI τ₃ τ₃ τ₁ e₁ (λ m → CPSVal m)) 
    -- CPSLet (cpsI τ₃ τ₃ τ₁ e₁ (λ m → CPSVal m)) (λ a → CPSApp (CPSVal k) (CPSVal (CPSVar a)))
  cpsI′ τ₁ τ₂ τ₃ {var} (NonVal (Let {τ₁ = τ₄} {τ₂ = .τ₁} {α = .τ₂} {β = β} {γ = .τ₃} e₁ e₂)) k =
    -- cpsI τ₄ β τ₃ e₁
    --   (λ n → CPSLet (CPSVal n) (λ x′ → cpsI′ τ₁ τ₂ β (e₂ x′) k))
    cpsI τ₄ β τ₃ e₁
         (λ m → CPSApp (CPSVal (CPSFun (λ c → cpsI′ τ₁ τ₂ β (e₂ c) k))) (CPSVal m))
  
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
    sVar=  : {τ₁ : cpstyp} {v : cpsvalue[ var ] τ₁} →
             cpsSubstVal (λ x → CPSVar x) v v
    sVar≠  : {τ₁ τ₂ : cpstyp} {v : cpsvalue[ var ] τ₂} {x : var τ₁} →
             cpsSubstVal (λ _ → CPSVar x) v (CPSVar x)
    sNum   : {τ₁ : cpstyp} {v : cpsvalue[ var ] τ₁} {n : ℕ} →
             cpsSubstVal (λ _ → CPSNum n) v (CPSNum n)
    sShift : {τ τ₁ τ₂ τ₃ τ₄ τ₅ : cpstyp} {v : cpsvalue[ var ] τ} →
             cpsSubstVal (λ _ → CPSShift {τ₁ = τ₁} {τ₂} {τ₃} {τ₄} {τ₅}) v CPSShift
    sFun   : {τ τ₁ τ₂ : cpstyp} →
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

mutual 
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
       eqShift : {τ₁ τ₂ τ₃ τ₄ τ₅ : cpstyp} →
                  {v : cpsvalue[ var ] ((τ₁ ⇒ ((τ₂ ⇒ τ₃) ⇒ τ₃)) ⇒ ((τ₄ ⇒ τ₄) ⇒ τ₅))} →
                  {k : cpsvalue[ var ] (τ₁ ⇒ τ₂)} →
                  cpsequal (CPSApp (CPSApp
                                   (CPSVal (CPSFun (λ w → CPSVal (CPSFun (λ k₁ →
                                     CPSApp (CPSApp (CPSVal (CPSVar w))
                                                    (CPSVal (CPSFun (λ a → CPSVal (CPSFun (λ k′ →
                                                      CPSApp (CPSVal (CPSVar k′))
                                                             (CPSApp (CPSVal (CPSVar k₁)) (CPSVal (CPSVar a)))))))))
                                            (CPSVal (CPSFun (λ m → CPSVal (CPSVar m)))))))))
                                   (CPSVal v)) (CPSVal k))
                           (CPSApp (CPSApp (CPSVal v) (CPSVal (CPSFun
                                      (λ a → CPSVal (CPSFun λ k′ →
                                        CPSApp (CPSVal (CPSVar k′)) (CPSApp (CPSVal k) (CPSVal (CPSVar a))))))))
                                   (CPSVal (CPSFun (λ m → CPSVal (CPSVar m)))))
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

