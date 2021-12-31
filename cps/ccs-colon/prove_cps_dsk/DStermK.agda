module DStermK where

open import Data.Nat

-- type
data typ𝑘 : Set where
  Nat          : typ𝑘
  Boolean      : typ𝑘
  _⇒_cps[_,_]  : typ𝑘 → typ𝑘 → typ𝑘 → typ𝑘 → typ𝑘

data typ𝑘𝑐 : Set where
  _⇒_cps[_] : typ𝑘 → typ𝑘 → typ𝑘 → typ𝑘𝑐

-- source kernel term
mutual

  data root𝑘[_]_cps[_,_] (var : typ𝑘 → Set) : typ𝑘 → typ𝑘 → typ𝑘 → Set where
    Root : {τ₁ τ₃ τ₄ : typ𝑘} →
           -- (var (τ₁ ⇒ τ₃ cps[ τ , τ ]) → term𝑘[ var ] τ₃ cps[ τ₃ , τ₄ ]) →
           -- term の周りに reset があるため、term の τ₃ を τ₂ に変更
           -- (var (τ₁ ⇒ τ₃ cps[ τ , τ ]) → term𝑘[ var ] τ₂ cps[ τ₂ , τ₄ ]) →
           (var (τ₁ ⇒ τ₃ cps[ τ₃ , τ₃ ]) → term𝑘[ var ] τ₃ cps[ τ₃ , τ₄ ]) →
           root𝑘[ var ] τ₁ cps[ τ₃ , τ₄ ]
           
  data value𝑘[_]_cps[τ,τ] (var : typ𝑘 → Set) : typ𝑘 → Set where
    Num   : ℕ → value𝑘[ var ] Nat cps[τ,τ]
    Var   : {τ₁ : typ𝑘} → var τ₁ → value𝑘[ var ] τ₁ cps[τ,τ]
    Fun   : (τ τ₁ τ₂ {τ₃ τ₄} : typ𝑘) →
            -- (var τ₂ → var (τ₁ ⇒ τ₃ cps[ τ , τ ]) → term𝑘[ var ] τ₃ cps[ τ₃ , τ₄ ]) →
            (var τ₄ → var (τ₁ ⇒ τ₃ cps[ τ , τ ]) → term𝑘[ var ] τ₂ cps[ τ₂ , τ₄ ]) →
            -- (var τ₂ → root𝑘[ var ] τ₁ cps[ τ₃ , τ₄ ]) →
            value𝑘[ var ] (τ₄ ⇒ τ₁ cps[ τ₃ , τ₄ ]) cps[τ,τ]
    Shift : {τ τ₁ τ₂ τ₃ τ₄ : typ𝑘} →
            value𝑘[ var ]
             (((τ₃ ⇒ τ₄ cps[ τ , τ ]) ⇒ τ₁ cps[ τ₁ , τ₂ ])
               ⇒ τ₃ cps[ τ₄ , τ₂ ])
               cps[τ,τ]

  data nonvalue𝑘[_]_cps[_,_] (var : typ𝑘 → Set) : typ𝑘 → typ𝑘 → typ𝑘 → Set where
    App   : {τ₁ τ₂ τ₃ τ₄ : typ𝑘} →
            value𝑘[ var ] τ₂ ⇒ τ₁ cps[ τ₃ , τ₄ ] cps[τ,τ] →
            value𝑘[ var ] τ₂ cps[τ,τ] → 
            nonvalue𝑘[ var ] τ₁ cps[ τ₃ , τ₄ ]
    Reset : (τ₁ τ₂ τ₃ : typ𝑘) →
            term𝑘[ var ] τ₁ cps[ τ₁ , τ₂ ] →
            nonvalue𝑘[ var ] τ₂ cps[ τ₃ , τ₃ ]

-- kがresetまでのコンテキストを全部含んでいるので、pcontext𝑘の外側の継続はidentity
-- τ₅ を τ₄ にした
  data term𝑘[_]_cps[_,_] (var : typ𝑘 → Set) : typ𝑘 → typ𝑘 → typ𝑘 → Set where
    Val    : {τ₁ τ₂ τ₄ : typ𝑘} →
             pcontext𝑘[ var , τ₁ cps[ τ₂ , τ₂ ]] τ₄
                     cps[ τ₄ , τ₂ ] →
             value𝑘[ var ] τ₁ cps[τ,τ] →
             term𝑘[ var ] τ₄ cps[ τ₄ , τ₂ ]
    NonVal : {τ₁ τ₂ τ₃ τ₄ : typ𝑘} →
             pcontext𝑘[ var , τ₁ cps[ τ₂ , τ₃ ]] τ₄
                     cps[ τ₄ , τ₃ ] →
             nonvalue𝑘[ var ] τ₁ cps[ τ₂ , τ₃ ] →
             term𝑘[ var ] τ₄ cps[ τ₄ , τ₃ ]
               
  data pcontext𝑘[_,_cps[_,_]]_cps[_,_] (var : typ𝑘 → Set)
       : typ𝑘 → typ𝑘 → typ𝑘 → typ𝑘 → typ𝑘 → typ𝑘 → Set where
    KHole : {τ₁ τ₂ τ₃ : typ𝑘} →
            -- (v₁ : var (τ₂ ⇒ τ₁ cps[ τ₃ , τ₃ ])) →
            (v₁ : var (τ₁ ⇒ τ₂ cps[ τ₂ , τ₂ ])) →
            pcontext𝑘[ var , τ₁ cps[ τ₂ , τ₃ ]] τ₂ cps[ τ₂ , τ₃ ]
    Hole  : {τ₁ τ₃ : typ𝑘} →
            pcontext𝑘[ var , τ₁ cps[ τ₁ , τ₃ ]] τ₁ cps[ τ₁ , τ₃ ]
    KLet  : {τ₁ τ₂ β γ : typ𝑘} →
            (e₂ : var τ₁ → term𝑘[ var ] τ₂ cps[ τ₂ , β ]) →
            pcontext𝑘[ var , τ₁ cps[ β , γ ]] τ₂ cps[ τ₂ , γ ]

-- mutual
  data SubstRootV𝑘 {var : typ𝑘 → Set} : {τ₁ τ₂ τ₃ τ₄ : typ𝑘} →
                   (var τ₁ → root𝑘[ var ] τ₂ cps[ τ₃ , τ₄ ]) →
                   value𝑘[ var ] τ₁ cps[τ,τ] →
                   root𝑘[ var ] τ₂ cps[ τ₃ , τ₄ ] → Set where
   sRoot : {τ τ₁ τ₃ τ₄ : typ𝑘} → 
           {r₁ : var τ → var (τ₁ ⇒ τ₃ cps[ τ₃ , τ₃ ]) → term𝑘[ var ] τ₃ cps[ τ₃ , τ₄ ]} →
           {v  : value𝑘[ var ] τ cps[τ,τ]} →
           {r₂ : var (τ₁ ⇒ τ₃ cps[ τ₃ , τ₃ ]) → term𝑘[ var ] τ₃ cps[ τ₃ , τ₄ ]} →
           ((k : var (τ₁ ⇒ τ₃ cps[ τ₃ , τ₃ ])) → SubstV𝑘 (λ y → (r₁ y) k) v (r₂ k)) →
           SubstRootV𝑘 (λ y → Root (r₁ y))
                       v
                       (Root r₂)

  data SubstValV𝑘 {var : typ𝑘 → Set} : {τ₁ τ₂ : typ𝑘} →
                  (var τ₁ → value𝑘[ var ] τ₂ cps[τ,τ]) →
                  value𝑘[ var ] τ₁ cps[τ,τ] →
                  value𝑘[ var ] τ₂ cps[τ,τ] → Set where
    sVar=  : {τ₁ : typ𝑘} {v : value𝑘[ var ] τ₁ cps[τ,τ]} →
           SubstValV𝑘 (λ x → Var x) v v
    sVar≠  : {τ₁ τ₂ : typ𝑘} {v : value𝑘[ var ] τ₂ cps[τ,τ]} {x : var τ₁} →
           SubstValV𝑘 (λ _ → Var x) v (Var x)
    sNum   : {τ₁ : typ𝑘} {v : value𝑘[ var ] τ₁ cps[τ,τ]} {n : ℕ} →
           SubstValV𝑘 (λ _ → Num n) v (Num n)
    sShift : {τ τ₁ τ₂ τ₃ τ₄ τ₅ : typ𝑘} {v : value𝑘[ var ] τ₅ cps[τ,τ]} →
           SubstValV𝑘 (λ _ → Shift {τ = τ} {τ₁} {τ₂} {τ₃} {τ₄}) v Shift
    sFun   : {τ τ₀ τ₁ τ₂ τ₃ τ₄ : typ𝑘} →
             {e₁  : var τ → var τ₄ → var (τ₁ ⇒ τ₃ cps[ τ₀ , τ₀ ]) → 
                    term𝑘[ var ] τ₂ cps[ τ₂ , τ₄ ]} →
             {v   : value𝑘[ var ] τ cps[τ,τ]} →
             {e₁′ : var τ₄ → var (τ₁ ⇒ τ₃ cps[ τ₀ , τ₀ ]) →
                    term𝑘[ var ] τ₂ cps[ τ₂ , τ₄ ]} →
             ((x : var τ₄) → (k : var (τ₁ ⇒ τ₃ cps[ τ₀ , τ₀ ])) →
              SubstV𝑘 (λ y → (e₁ y) x k) v (e₁′ x k)) →
             SubstValV𝑘 (λ y → Fun τ₀ τ₁ τ₂ (λ k → e₁ y k))
                       v
                       (Fun τ₀ τ₁ τ₂ e₁′)

  data SubstConV𝑘 {var : typ𝑘 → Set} : {τ τ₁ τ₂ τ₃ τ₄ : typ𝑘} →
                  (var τ → pcontext𝑘[ var , τ₁ cps[ τ₂ , τ₃ ]] τ₄
                                    cps[ τ₄ , τ₃ ]) →
                  value𝑘[ var ] τ cps[τ,τ] →
                  pcontext𝑘[ var , τ₁ cps[ τ₂ , τ₃ ]] τ₄
                          cps[ τ₄ , τ₃ ] → Set where
    sConVar≠ : {τ τ₁ τ₂ τ₃ : typ𝑘} →
               -- 型???
               {k′ : var (τ₁ ⇒ τ₂ cps[ τ₂ , τ₂ ])} → 
               {v : value𝑘[ var ] τ cps[τ,τ]} →
               SubstConV𝑘 {τ₃ = τ₃} (λ _ → KHole k′) v (KHole k′)
    sConId     : {τ τ₁ τ₃ : typ𝑘} →
               {v : value𝑘[ var ] τ cps[τ,τ]} →
               SubstConV𝑘 {τ₁ = τ₁} {τ₃ = τ₃} (λ _ → Hole) v Hole 
    sConLet  : {τ τ₁ τ₂ β γ : typ𝑘} →
               {e₁ : var τ → var τ₁ → term𝑘[ var ] τ₂ cps[ τ₂ , β ]} →  
               {v  : value𝑘[ var ] τ cps[τ,τ]}→
               {e₂ : var τ₁ → term𝑘[ var ] τ₂ cps[ τ₂ , β ]} →
               ((x : var τ₁) → SubstV𝑘 (λ y → (e₁ y) x) v (e₂ x)) → 
               SubstConV𝑘 {τ₃ = γ} (λ y → KLet (λ x → (e₁ y) x))
                          v
                          (KLet (λ x → e₂ x)) 


  data SubstV𝑘 {var : typ𝑘 → Set} : {τ₁ τ₂ τ₄ : typ𝑘} →
               (var τ₁ → term𝑘[ var ] τ₂ cps[ τ₂ , τ₄ ]) →
               value𝑘[ var ] τ₁ cps[τ,τ] →
               term𝑘[ var ] τ₂ cps[ τ₂ , τ₄ ] → Set where
    sVal   : {τ τ₁ τ₂ τ₄ : typ𝑘} →
             {k₁ : var τ →
                   pcontext𝑘[ var , τ₁ cps[ τ₂ , τ₂ ]] τ₄
                          cps[ τ₄ , τ₂ ]} →
             {v₁ : var τ → value𝑘[ var ] τ₁ cps[τ,τ]} → 
             {v : value𝑘[ var ] τ cps[τ,τ]} →
             {k₂ : pcontext𝑘[ var , τ₁ cps[ τ₂ , τ₂ ]] τ₄
                          cps[ τ₄ , τ₂ ]} →
             {v₂ : value𝑘[ var ] τ₁ cps[τ,τ]} →
             SubstConV𝑘 k₁ v k₂ → SubstValV𝑘 v₁ v v₂ → 
             SubstV𝑘 (λ y → Val (k₁ y) (v₁ y)) v (Val k₂ v₂)
    sApp   : {τ τ₁ τ₂ τ₃ τ₄ τ₅ : typ𝑘} →
             {k₁ : var τ →
                   pcontext𝑘[ var , τ₁ cps[ τ₃ , τ₄ ]] τ₅
                           cps[ τ₅ , τ₄ ]} → 
             {v₁ : var τ → value𝑘[ var ] τ₂ ⇒ τ₁ cps[ τ₃ , τ₄ ] cps[τ,τ]} →
             {w₁ : var τ → value𝑘[ var ] τ₂ cps[τ,τ]} →
             {v  : value𝑘[ var ] τ cps[τ,τ]} →
             {k₂ : pcontext𝑘[ var , τ₁ cps[ τ₃ , τ₄ ]] τ₅
                           cps[ τ₅ , τ₄ ]} → 
             {v₂ : value𝑘[ var ] τ₂ ⇒ τ₁ cps[ τ₃ , τ₄ ] cps[τ,τ]} →
             {w₂ : value𝑘[ var ] τ₂ cps[τ,τ]} →
             SubstConV𝑘 k₁ v k₂ → SubstValV𝑘 v₁ v v₂ → SubstValV𝑘 w₁ v w₂ → 
             SubstV𝑘 (λ y → NonVal (k₁ y) (App (v₁ y) (w₁ y)))
                    v
                    (NonVal k₂ (App v₂ w₂))
    sReset : {τ τ₁ τ₂ τ₃ τ₅ : typ𝑘} →
             {k₁ : var τ →
                   pcontext𝑘[ var , τ₂ cps[ τ₃ , τ₃ ]] τ₅
                           cps[ τ₅ , τ₃ ]} →
             {e₁ : var τ → term𝑘[ var ] τ₁ cps[ τ₁ , τ₂ ]} → 
             {v  : value𝑘[ var ] τ cps[τ,τ]} →
             {k₂ : pcontext𝑘[ var , τ₂ cps[ τ₃ , τ₃ ]] τ₅
                           cps[ τ₅ , τ₃ ]} →
             {e₂ : term𝑘[ var ] τ₁ cps[ τ₁ , τ₂ ]} →
             SubstConV𝑘 k₁ v k₂ → SubstV𝑘 e₁ v e₂ → 
             SubstV𝑘 (λ y → NonVal (k₁ y) (Reset τ₁ τ₂ τ₃ (e₁ y)))
                    v
                    (NonVal k₂ (Reset τ₁ τ₂ τ₃ e₂))

mutual
  data SubstCon𝑘 {var : typ𝑘 → Set} : {τ τ₁ τ₂ τ₃ τ₇ α β γ ζ : typ𝑘} →
                 (var τ → var (α ⇒ β cps[ ζ , ζ ]) →
                   pcontext𝑘[ var , τ₁ cps[ τ₂ , τ₃ ]] τ₇ cps[ τ₇ , τ₃ ]) →
                 value𝑘[ var ] τ cps[τ,τ] →
                 pcontext𝑘[ var , α cps[ β , γ ]] ζ cps[ ζ , γ ] →
                 pcontext𝑘[ var , τ₁ cps[ τ₂ , τ₃ ]] τ₇ cps[ τ₇ , τ₃ ] → Set where

    sCon= : {τ τ₁ τ₂ τ₃ : typ𝑘} →
            {v  : value𝑘[ var ] τ cps[τ,τ]} → 
            {K𝑐 : pcontext𝑘[ var , τ₁ cps[ τ₂ , τ₃ ]] τ₂ cps[ τ₂ , τ₃ ]} →
            SubstCon𝑘 (λ _ k → KHole k) v K𝑐 K𝑐
    sCon≠ : {τ τ₁ τ₂ τ₅ α β γ ζ : typ𝑘} →
            {v  : value𝑘[ var ] τ cps[τ,τ]} → 
            {K𝑐 : pcontext𝑘[ var , α cps[ β , γ ]] ζ cps[ ζ , γ ]} →
            {k′ : var (τ₂ ⇒ τ₁ cps[ τ₁ , τ₁ ])} → 
            SubstCon𝑘 {τ₃ = τ₅} (λ _ _ → KHole k′) v K𝑐 (KHole k′)
    sHole : {τ τ₁ τ₃ α β γ ζ : typ𝑘} →
            {v  : value𝑘[ var ] τ cps[τ,τ]} → 
            {K𝑐 : pcontext𝑘[ var , α cps[ β , γ ]] ζ cps[ ζ , γ ]} → 
            SubstCon𝑘 {τ₁ = τ₁} {τ₃ = τ₃} (λ _ _ → Hole) v K𝑐 Hole
    sLet  : {τ τ₁ τ₂ τ₃ τ₄ α β γ ζ : typ𝑘} →            
            {e  : var τ → var (α ⇒ β cps[ ζ , ζ ]) → (var τ₁ → term𝑘[ var ] τ₄ cps[ τ₄ , τ₂ ])} →
            {v  : value𝑘[ var ] τ cps[τ,τ]} → 
            {K𝑐 : pcontext𝑘[ var , α cps[ β , γ ]] ζ cps[ ζ , γ ]} →
            {e′ : var τ₁ → term𝑘[ var ] τ₄ cps[ τ₄ , τ₂ ]} →
            ((x : var τ₁) → Subst𝑘 (λ y k′ → (e y k′) x) v K𝑐 (e′ x)) → 
            SubstCon𝑘 {τ₃ = τ₃} (λ y k′ → KLet (e y k′))
                                 v K𝑐
                                 (KLet e′)

  data Subst𝑘 {var : typ𝑘 → Set} : {τ τ₂ τ₃ α β γ ζ : typ𝑘} →
              (var τ → var (α ⇒ β cps[ ζ , ζ ]) → term𝑘[ var ] τ₂ cps[ τ₂ , τ₃ ]) →
              value𝑘[ var ] τ cps[τ,τ] →
              pcontext𝑘[ var , α cps[ β , γ ]] ζ cps[ ζ , γ ] → 
              term𝑘[ var ] τ₂ cps[ τ₂ , τ₃ ] → Set where
    sVal  : {τ τ₁ τ₂ τ₄ α β γ ζ : typ𝑘} →
               {k₁ : var τ → var (α ⇒ β cps[ ζ , ζ ]) →
                   pcontext𝑘[ var , τ₁ cps[ τ₂ , τ₂ ]] τ₄
                           cps[ τ₄ , τ₂ ]} →
               {v₁ : var τ → value𝑘[ var ] τ₁ cps[τ,τ]} →
               {v  : value𝑘[ var ] τ cps[τ,τ]} →
               {K𝑐 : pcontext𝑘[ var , α cps[ β , γ ]] ζ cps[ ζ , γ ]} →
               {k₂ : pcontext𝑘[ var , τ₁ cps[ τ₂ , τ₂ ]] τ₄
                             cps[ τ₄ , τ₂ ]} →
               {v₂ : value𝑘[ var ] τ₁ cps[τ,τ]} →
               SubstCon𝑘 k₁ v K𝑐 k₂ → SubstValV𝑘 v₁ v v₂ → 
               Subst𝑘 (λ y k′ → Val (k₁ y k′) (v₁ y)) v K𝑐 (Val k₂ v₂)
    sApp   : {τ τ₁ τ₂ τ₃ τ₄ τ₅ α β γ ζ : typ𝑘} →
             {k₁ : var τ → var (α ⇒ β cps[ ζ , ζ ]) → 
                   pcontext𝑘[ var , τ₁ cps[ τ₃ , τ₄ ]] τ₅
                           cps[ τ₅ , τ₄ ]} → 
             {v₁ : var τ → value𝑘[ var ] τ₂ ⇒ τ₁ cps[ τ₃ , τ₄ ] cps[τ,τ]} →
             {w₁ : var τ → value𝑘[ var ] τ₂ cps[τ,τ]} →
             {v  : value𝑘[ var ] τ cps[τ,τ]} →
             {K𝑐 : pcontext𝑘[ var , α cps[ β , γ ]] ζ cps[ ζ , γ ]} → 
             {k₂ : pcontext𝑘[ var , τ₁ cps[ τ₃ , τ₄ ]] τ₅
                           cps[ τ₅ , τ₄ ]} → 
             {v₂ : value𝑘[ var ] τ₂ ⇒ τ₁ cps[ τ₃ , τ₄ ] cps[τ,τ]} →
             {w₂ : value𝑘[ var ] τ₂ cps[τ,τ]} →
             SubstCon𝑘 k₁ v K𝑐 k₂ → SubstValV𝑘 v₁ v v₂ → SubstValV𝑘 w₁ v w₂ → 
             Subst𝑘 (λ y k′  → NonVal (k₁ y k′) (App (v₁ y) (w₁ y)))
                    v K𝑐
                    (NonVal k₂ (App v₂ w₂))
    sReset : {τ τ₁ τ₂ τ₃ τ₅ α β γ ζ : typ𝑘} →
             {k₁ : var τ → var (α ⇒ β cps[ ζ , ζ ]) → 
                   pcontext𝑘[ var , τ₂ cps[ τ₃ , τ₃ ]] τ₅
                           cps[ τ₅ , τ₃ ]} →
             {e₁ : var τ → var (α ⇒ β cps[ ζ , ζ ]) → term𝑘[ var ] τ₁ cps[ τ₁ , τ₂ ]} → 
             {v  : value𝑘[ var ] τ cps[τ,τ]} →
             {K𝑐 : pcontext𝑘[ var , α cps[ β , γ ]] ζ cps[ ζ , γ ]} → 
             {k₂ : pcontext𝑘[ var , τ₂ cps[ τ₃ , τ₃ ]] τ₅
                           cps[ τ₅ , τ₃ ]} →
             {e₂ : term𝑘[ var ] τ₁ cps[ τ₁ , τ₂ ]} →
             SubstCon𝑘 k₁ v K𝑐 k₂ → Subst𝑘 e₁ v K𝑐 e₂ → 
             Subst𝑘 (λ y k′ → NonVal (k₁ y k′) (Reset τ₁ τ₂ τ₃ (e₁ y k′)))
                    v K𝑐 
                    (NonVal k₂ (Reset τ₁ τ₂ τ₃ e₂))

data ReduceRoot𝑘 {var : typ𝑘 → Set} :
                 {τ τ₁ τ₂ τ₃ τ₄ : typ𝑘} →
                 (var (τ₁ ⇒ τ₃ cps[ τ , τ ]) → term𝑘[ var ] τ₂ cps[ τ₂ , τ₄ ]) →
                 (var (τ₁ ⇒ τ₃ cps[ τ , τ ]) → term𝑘[ var ] τ₂ cps[ τ₂ , τ₄ ]) → Set where
                 -- root𝑘[ var ] τ₁ cps[ τ₂ , τ₃ ] → Set where
     βVal  : {τ′ τ₁′ τ₃′ τ₀ τ₁ τ₂ τ₃ τ₄ α ζ : typ𝑘} →
              {K𝑐 : pcontext𝑘[ var , τ₁ cps[ τ₃ , τ₄ ]] τ₀ cps[ τ₀ , τ₄ ]} →
              {e  : var τ₄ → var (τ₁ ⇒ τ₃ cps[ τ₀ , τ₀ ]) →
                    term𝑘[ var ] τ₂ cps[ τ₂ , τ₄ ]} →
              {v  : value𝑘[ var ] τ₄ cps[τ,τ]} →
              {e′ : term𝑘[ var ] τ₂ cps[ τ₂ , τ₄ ]} →
              Subst𝑘 e v K𝑐 e′ →
              ReduceRoot𝑘 {τ = τ′} {τ₁ = τ₁′} {τ₃ = τ₃′}
                (λ k → NonVal Hole (Reset τ₀ τ₄ τ₄
                       (NonVal K𝑐
                               (App (Fun τ₀ τ₁ τ₄ (λ x k′ →
                                         NonVal Hole (Reset τ₂ τ₄ τ₄ (e x k′))))
                                    v))))
                (λ k → NonVal Hole (Reset τ₂ τ₄ τ₄ e′))

data ReduceTerm𝑘 {var : typ𝑘 → Set} :
                 {τ₂ τ₃ : typ𝑘} →
                 term𝑘[ var ] τ₂ cps[ τ₂ , τ₃ ] →
                 term𝑘[ var ] τ₂ cps[ τ₂ , τ₃ ] → Set where
     βLet : {τ₁ τ₂ β : typ𝑘} →
             {e₂  : var τ₁ → term𝑘[ var ] τ₂ cps[ τ₂ , β ]} →
             {v   : value𝑘[ var ] τ₁ cps[τ,τ]} →
             {e₂′ : term𝑘[ var ] τ₂ cps[ τ₂ , β ]} →
             SubstV𝑘 (λ x → e₂ x) v e₂′ → 
             ReduceTerm𝑘 (Val (KLet e₂) v) e₂′

data ReduceTerm𝑘𝑠 {var : typ𝑘 → Set} : 
                  {τ₂ τ₃ : typ𝑘} →
                  term𝑘[ var ] τ₂ cps[ τ₂ , τ₃ ] →
                  term𝑘[ var ] τ₂ cps[ τ₂ , τ₃ ] → Set where
     βShift : {τ₁ τ₃ τ₄ : typ𝑘} →
               {J : pcontext𝑘[ var , τ₃ cps[ τ₄ , τ₄ ]] τ₁ cps[ τ₁ , τ₄ ]} →
               {w : value𝑘[ var ] (τ₃ ⇒ τ₄ cps[ τ₃ , τ₃ ]) ⇒ τ₁ cps[ τ₁ , τ₄ ] cps[τ,τ]} →
               ReduceTerm𝑘𝑠
                 (NonVal Hole (Reset τ₁ τ₄ τ₄
                         (NonVal J
                                 (App Shift w))))
                 (NonVal Hole (Reset τ₁ τ₄ τ₄
                         (NonVal Hole
                                 (App w
                                      (Fun τ₃ τ₄ τ₃ (λ y k →
                                           NonVal Hole
                                                  (Reset τ₃ τ₃ τ₃
                                                         (NonVal (KHole k)
                                                                 (Reset τ₁ τ₄ τ₃
                                                                        (Val J (Var y)))))))))))
                                                                        
data ReduceTerm𝑘𝑅 {var : typ𝑘 → Set} :
                  {τ₂ : typ𝑘} →
                  term𝑘[ var ] τ₂ cps[ τ₂ , τ₂ ] →
                  value𝑘[ var ] τ₂ cps[τ,τ] → Set where
     βReset : {τ₁ : typ𝑘} →
               {v : value𝑘[ var ] τ₁ cps[τ,τ]} →
               ReduceTerm𝑘𝑅 (NonVal Hole (Reset τ₁ τ₁ τ₁ (Val Hole v)))
                            v
                    

data ReduceVal𝑘 {var : typ𝑘 → Set} :
                 {τ₁ : typ𝑘} →
                 value𝑘[ var ] τ₁ cps[τ,τ] →
                 value𝑘[ var ] τ₁ cps[τ,τ] → Set where
     ηVal : {τ₁ τ₂ τ₃ τ₄ : typ𝑘} →
             {v : value𝑘[ var ] τ₄ ⇒ τ₁ cps[ τ₃ , τ₄ ] cps[τ,τ]} →
             ReduceVal𝑘 (Fun τ₃ τ₁ τ₃ (λ x k →
                             NonVal (KHole k) (App v (Var x))))
                        v

data ReduceCon𝑘 {var : typ𝑘 → Set} :
                {τ₁ τ₂ τ₃ τ₇ : typ𝑘} →
                 pcontext𝑘[ var , τ₁ cps[ τ₂ , τ₃ ]] τ₇ cps[ τ₇ , τ₃ ] →
                 pcontext𝑘[ var , τ₁ cps[ τ₂ , τ₃ ]] τ₇ cps[ τ₇ , τ₃ ] → Set where
     ηLet : {τ₁ τ₂ β : typ𝑘} →
             {K𝑐 : pcontext𝑘[ var , τ₁ cps[ β , β ]] τ₂ cps[ τ₂ , β ]} → 
             ReduceCon𝑘 (KLet (λ x → Val K𝑐 (Var x)))
                        K𝑐
