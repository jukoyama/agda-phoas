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
           -- CHECK : 本当に τ を τ₃ にして大丈夫だろうか
           -- (var (τ₁ ⇒ τ₃ cps[ τ , τ ]) → term𝑘[ var ] τ₃ cps[ τ₃ , τ₄ ]) →
           (var (τ₁ ⇒ τ₃ cps[ τ₃ , τ₃ ]) → term𝑘[ var ] τ₃ cps[ τ₃ , τ₄ ]) →
           -- term𝑘[ var ] τ₃ cps[ τ₃ , τ₄ ] → 
           root𝑘[ var ] τ₁ cps[ τ₃ , τ₄ ]
           
  data value𝑘[_]_cps[τ,τ] (var : typ𝑘 → Set) : typ𝑘 → Set where
    Num   : ℕ → value𝑘[ var ] Nat cps[τ,τ]
    Var   : {τ₁ : typ𝑘} → var τ₁ → value𝑘[ var ] τ₁ cps[τ,τ]
    Fun   : (τ₁ τ₂ {τ₃ τ₄} : typ𝑘) →
            -- (var τ₂ → var (τ₁ ⇒ τ₃ cps[ τ , τ ]) → term𝑘[ var ] τ₃ cps[ τ₃ , τ₄ ]) →
            (var τ₂ → root𝑘[ var ] τ₁ cps[ τ₃ , τ₄ ]) →
            -- (var τ₂ → term𝑘[ var ] τ₃ cps[ τ₃ , τ₄ ]) → 
            value𝑘[ var ] (τ₂ ⇒ τ₁ cps[ τ₃ , τ₄ ]) cps[τ,τ]
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
             
  data pframe𝑘[_,_cps[_,_]]_cps[_,_] (var : typ𝑘 → Set)
       : typ𝑘 → typ𝑘 → typ𝑘 → typ𝑘 → typ𝑘 → typ𝑘 → Set where
    App₂ : {τ₁ τ₂ τ₃ τ₅ : typ𝑘} →
           (v₁ : var (τ₂ ⇒ τ₁ cps[ τ₃ , τ₃ ])) →
           pframe𝑘[ var , τ₂ cps[ τ₃ , τ₅ ]] τ₁ cps[ τ₃ , τ₅ ]
    -- Let  : {τ₁ τ₂ α β γ : typ𝑘} →
    --        (e₂ : var τ₁ → term𝑘[ var ] τ₂ cps[ α , β ]) →
    --        pframe𝑘[ var , τ₁ cps[ β , γ ]] τ₂ cps[ α , γ ]
    -- sConLet で α = τ₂ にしないとまずい？？
    Let  : {τ₁ τ₂ β γ : typ𝑘} →
           (e₂ : var τ₁ → term𝑘[ var ] τ₂ cps[ τ₂ , β ]) →
           pframe𝑘[ var , τ₁ cps[ β , γ ]] τ₂ cps[ τ₂ , γ ]

  -- data pcontext𝑘[_,_cps[_,_]]_cps[_,_] (var : typ𝑘 → Set)
  --      : typ𝑘 → typ𝑘 → typ𝑘 → typ𝑘 → typ𝑘 → typ𝑘 → Set where
  --   Hole  : {τ₁ τ₂ τ₃ : typ𝑘} →
  --           pcontext𝑘[ var , τ₁ cps[ τ₂ , τ₃ ]] τ₁ cps[ τ₂ , τ₃ ]
  --   Frame : {τ₁ τ₂ τ₃ τ₄ τ₅ τ₆ τ₇ τ₈ τ₉ : typ𝑘} →
  --           (f : pframe𝑘[ var , τ₄ cps[ τ₅ , τ₆ ]] τ₇
  --                    cps[ τ₈ , τ₉ ]) →
  --           (e : pcontext𝑘[ var , τ₁ cps[ τ₂ , τ₃ ]] τ₄
  --                      cps[ τ₅ , τ₆ ]) →
  --           pcontext𝑘[ var , τ₁ cps[ τ₂ , τ₃ ]] τ₇ cps[ τ₈ , τ₉ ]
  
-- τは、帰納的に同じになる
  data pcontext𝑘[_,_cps[_,_]]_cps[_,_] (var : typ𝑘 → Set)
       : typ𝑘 → typ𝑘 → typ𝑘 → typ𝑘 → typ𝑘 → typ𝑘 → Set where
    -- Hole𝑘 : {τ₁ τ₂ τ₃ : typ𝑘} →
    --         pcontext𝑘[ var , τ₁ cps[ τ₂ , τ₃ ]] τ₂ cps[ τ₂ , τ₃ ]
    Hole  : {τ₁ τ₂ τ₃ : typ𝑘} →
            pcontext𝑘[ var , τ₁ cps[ τ₂ , τ₃ ]] τ₁ cps[ τ₂ , τ₃ ]
    Frame : {τ τ₁ τ₂ τ₇ τ₈ : typ𝑘} →
            (f : pframe𝑘[ var , τ₁ cps[ τ₂ , τ ]] τ₇
                     cps[ τ₈ , τ ]) →
            (e : pcontext𝑘[ var , τ₁ cps[ τ₂ , τ ]] τ₁
                       cps[ τ₂ , τ ]) →
            pcontext𝑘[ var , τ₁ cps[ τ₂ , τ ]] τ₇ cps[ τ₈ , τ ]

  data pcontext2𝑘[_,_cps[_,_]]_cps[_,_] (var : typ𝑘 → Set)
       : typ𝑘 → typ𝑘 → typ𝑘 → typ𝑘 → typ𝑘 → typ𝑘 → Set where
    KHole : {τ₁ τ₂ τ₃ τ₅ : typ𝑘} →
            (v₁ : var (τ₂ ⇒ τ₁ cps[ τ₃ , τ₃ ])) →
            pcontext2𝑘[ var , τ₂ cps[ τ₃ , τ₅ ]] τ₁ cps[ τ₃ , τ₅ ]
    Hole  : {τ₁ τ₂ τ₃ : typ𝑘} →
            pcontext2𝑘[ var , τ₁ cps[ τ₁ , τ₃ ]] τ₁ cps[ τ₁ , τ₃ ]
    KLet  : {τ₁ τ₂ β γ : typ𝑘} →
            (e₂ : var τ₁ → term𝑘[ var ] τ₂ cps[ τ₂ , β ]) →
            pcontext2𝑘[ var , τ₁ cps[ β , γ ]] τ₂ cps[ τ₂ , γ ]

-- data same-pframe𝑘 {var : typ𝑘 → Set} :
--                  {τ₁ τ₁' τ₂ τ₂' τ₃ τ₃' τ₄ τ₄' τ₅ τ₅' τ₆ τ₆' : typ𝑘} →
--        pframe𝑘[ var , τ₁ cps[ τ₂ , τ₃ ]] τ₄ cps[ τ₅ , τ₆ ] →
--        pframe𝑘[ var , τ₁' cps[ τ₂' , τ₃' ]] τ₄' cps[ τ₅' , τ₆' ] →
--        Set where
--   Let  : {τ₇ τ₈ τ₉ τ₁₀ τ₃ τ₃' : typ𝑘} →
--          (e₂ : var τ₈ → term𝑘[ var ] τ₇ cps[ τ₉ , τ₁₀ ]) →
--          same-pframe𝑘 {τ₃ = τ₃}{τ₃'}
--                      (Let e₂) (Let e₂)


-- data same-pcontext𝑘 {var : typ𝑘 → Set} :
--                    {τ₁ τ₁' τ₂ τ₂' τ₃ τ₃' τ₄ τ₄' τ₅ τ₅' τ₆ τ₆' : typ𝑘} →
--        pcontext𝑘[ var , τ₁ cps[ τ₂ , τ₃ ]] τ₄ cps[ τ₅ , τ₆ ] →
--        pcontext𝑘[ var , τ₁' cps[ τ₂' , τ₃' ]] τ₄' cps[ τ₅' , τ₆' ] →
--        Set where
--   Hole  : {τ₁ τ₁' τ₂ τ₂' τ₃ τ₃' : typ𝑘} →
--           same-pcontext𝑘 {τ₁ = τ₁}{τ₁'}{τ₂}{τ₂'}{τ₃}{τ₃'}
--                          Hole Hole
--   Frame : {τ₁ τ₁' τ₂ τ₂' τ₃ τ₃' τ₄ τ₄' τ₅ τ₅' τ₆ τ₆' τ₇ τ₇' τ₈ τ₈' τ₉ τ₉' : typ𝑘} →
--           {f₁ : pframe𝑘[ var , τ₄ cps[ τ₅ , τ₆ ]] τ₇
--                       cps[ τ₈ , τ₉ ]} →
--           {f₂ : pframe𝑘[ var , τ₄' cps[ τ₅' , τ₆' ]] τ₇'
--                       cps[ τ₈' , τ₉' ]} →
--           same-pframe𝑘 f₁ f₂ →
--           {p₁ : pcontext𝑘[ var , τ₁ cps[ τ₂ , τ₃ ]] τ₄
--                         cps[ τ₅ , τ₆ ]} →
--           {p₂ : pcontext𝑘[ var , τ₁' cps[ τ₂' , τ₃' ]] τ₄'
--                         cps[ τ₅' , τ₆' ]} →
--           same-pcontext𝑘 p₁ p₂ →
--           same-pcontext𝑘 (Frame f₁ p₁) (Frame f₂ p₂)


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
    sFun   : {τ τ₁ τ₂ τ₃ τ₄ : typ𝑘} →
             {e₁  : var τ₁ → var τ → root𝑘[ var ] τ₂ cps[ τ₃ , τ₄ ]} →
             {v   : value𝑘[ var ] τ₁ cps[τ,τ]} →
             {e₁′ : var τ → root𝑘[ var ] τ₂ cps[ τ₃ , τ₄ ]} →
             ((x : var τ) → SubstRootV𝑘 (λ y → (e₁ y) x) v (e₁′ x)) →
             SubstValV𝑘 (λ y → Fun τ₂ τ (e₁ y))
                        v
                        (Fun τ₂ τ e₁′)

  data SubstConV𝑘 {var : typ𝑘 → Set} : {τ τ₁ τ₂ τ₃ τ₄ : typ𝑘} →
                  (var τ → pcontext𝑘[ var , τ₁ cps[ τ₂ , τ₃ ]] τ₄
                                    cps[ τ₄ , τ₃ ]) →
                  value𝑘[ var ] τ cps[τ,τ] →
                  pcontext𝑘[ var , τ₁ cps[ τ₂ , τ₃ ]] τ₄
                          cps[ τ₄ , τ₃ ] → Set where
    sConVar≠ : {τ τ₁ τ₂ : typ𝑘} →
               -- 型???
               {k′ : var (τ₂ ⇒ τ₁ cps[ τ₁ , τ₁ ])} → 
               {v : value𝑘[ var ] τ cps[τ,τ]} →
               SubstConV𝑘 {τ₃ = τ₁} (λ _ → Frame (App₂ k′) Hole) v (Frame (App₂ k′) Hole)
    sConLet  : {τ τ₁ τ₂ β γ : typ𝑘} →
               {e₁ : var τ → var τ₁ → term𝑘[ var ] τ₂ cps[ τ₂ , β ]} →  
               {v  : value𝑘[ var ] τ cps[τ,τ]}→
               {e₂ : var τ₁ → term𝑘[ var ] τ₂ cps[ τ₂ , β ]} →  
               SubstConV𝑘 {τ₃ = γ} (λ y → Frame (Let λ x → (e₁ y) x) Hole)
                          v
                          (Frame (Let (λ x → e₂ x)) Hole) 


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
    sReset : {τ τ₁ τ₂ τ₃ τ₄ τ₅ : typ𝑘} →
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
  data SubstCon𝑘 {var : typ𝑘 → Set} : {τ τ₁ τ₂ τ₃ τ₇ τ₈ α β γ ε ζ : typ𝑘} →
                 (var τ → var (α ⇒ ε cps[ β , ζ ]) →
                   pcontext𝑘[ var , τ₁ cps[ τ₂ , τ₃ ]] τ₇ cps[ τ₈ , τ₃ ]) →
                 value𝑘[ var ] τ cps[τ,τ] →
                 pcontext𝑘[ var , α cps[ β , γ ]] ε cps[ ζ , γ ] →
                 pcontext𝑘[ var , τ₁ cps[ τ₂ , τ₃ ]] τ₇ cps[ τ₈ , τ₃ ] → Set where

    sCon= : {τ τ₁ τ₂ τ₃ τ₅ α β γ ε : typ𝑘} →
            {v  : value𝑘[ var ] τ cps[τ,τ]} → 
            {K𝑐 : pcontext𝑘[ var , α cps[ β , γ ]] ε cps[ β , γ ]} →
            SubstCon𝑘 (λ _ k → Frame (App₂ k) Hole) v K𝑐 K𝑐
    sCon≠ : {τ τ₁ τ₂ τ₃ τ₅ α β γ ε ζ : typ𝑘} →
            {v  : value𝑘[ var ] τ cps[τ,τ]} → 
            {K𝑐 : pcontext𝑘[ var , α cps[ β , γ ]] ε cps[ ζ , γ ]} →
            {k′ : var (τ₂ ⇒ τ₁ cps[ τ₃ , τ₃ ])} → 
            SubstCon𝑘 {τ₃ = τ₅} (λ _ _ → Frame (App₂ k′) Hole) v K𝑐 (Frame (App₂ k′) Hole)
    sHole : {τ τ₁ τ₂ τ₃ α β γ ε ζ : typ𝑘} →
            {v  : value𝑘[ var ] τ cps[τ,τ]} → 
            {K𝑐 : pcontext𝑘[ var , α cps[ β , γ ]] ε cps[ ζ , γ ]} → 
            SubstCon𝑘 {τ₁ = τ₁} {τ₂} {τ₃} (λ _ _ → Hole) v K𝑐 Hole
    sLet  : {τ τ₁ τ₂ β γ α′ β′ γ′ ε′ ζ′ : typ𝑘} →
            (e  : var τ → var (α′ ⇒ ε′ cps[ β′ , ζ′ ]) → var τ₁ → term𝑘[ var ] τ₂ cps[ τ₂ , β ]) →
            {v  : value𝑘[ var ] τ cps[τ,τ]} → 
            {K𝑐 : pcontext𝑘[ var , α′ cps[ β′ , γ′ ]] ε′ cps[ ζ′ , γ′ ]} →
            (e′ : var τ₁ → term𝑘[ var ] τ₂ cps[ τ₂ , β ]) →
            ((x : var τ₁) → Subst𝑘 (λ y k′ → (e y k′) x) v K𝑐 (e′ x)) → 
            SubstCon𝑘 {τ₃ = γ′}
                      (λ y k′ → Frame (Let (e y k′)) Hole)
                      v K𝑐
                      (Frame (Let e′) Hole)

  data Subst𝑘 {var : typ𝑘 → Set} : {τ₁ τ₂ τ₃ τ₄ α β γ ε ζ : typ𝑘} →
              (var τ₁ → var (α ⇒ ε cps[ β , ζ ]) → term𝑘[ var ] τ₂ cps[ τ₃ , τ₄ ]) →
              value𝑘[ var ] τ₁ cps[τ,τ] →
              pcontext𝑘[ var , α cps[ β , γ ]] ε cps[ ζ , γ ] → 
              term𝑘[ var ] τ₂ cps[ τ₃ , τ₄ ] → Set where
    sVal  : {τ τ₁ τ₂ τ₄ α β γ ε ζ : typ𝑘} →
               {k₁ : var τ → var (α ⇒ ε cps[ β , ζ ]) →
                   pcontext𝑘[ var , τ₁ cps[ τ₂ , τ₂ ]] τ₄
                           cps[ τ₄ , τ₂ ]} →
               {v₁ : var τ → value𝑘[ var ] τ₁ cps[τ,τ]} →
               {v  : value𝑘[ var ] τ cps[τ,τ]} →
               {K𝑐 : pcontext𝑘[ var , α cps[ β , γ ]] ε cps[ ζ , γ ]} →
               {k₂ : pcontext𝑘[ var , τ₁ cps[ τ₂ , τ₂ ]] τ₄
                             cps[ τ₄ , τ₂ ]} →
               {v₂ : value𝑘[ var ] τ₁ cps[τ,τ]} →
               SubstCon𝑘 k₁ v K𝑐 k₂ → SubstValV𝑘 v₁ v v₂ → 
               Subst𝑘 (λ y k′ → Val (k₁ y k′) (v₁ y)) v K𝑐 (Val k₂ v₂)
    sApp   : {τ τ₁ τ₂ τ₃ τ₄ τ₅ α β γ ε ζ : typ𝑘} →
             {k₁ : var τ → var (α ⇒ ε cps[ β , ζ ]) → 
                   pcontext𝑘[ var , τ₁ cps[ τ₃ , τ₄ ]] τ₅
                           cps[ τ₅ , τ₄ ]} → 
             {v₁ : var τ → value𝑘[ var ] τ₂ ⇒ τ₁ cps[ τ₃ , τ₄ ] cps[τ,τ]} →
             {w₁ : var τ → value𝑘[ var ] τ₂ cps[τ,τ]} →
             {v  : value𝑘[ var ] τ cps[τ,τ]} →
             {K𝑐 : pcontext𝑘[ var , α cps[ β , γ ]] ε cps[ ζ , γ ]} → 
             {k₂ : pcontext𝑘[ var , τ₁ cps[ τ₃ , τ₄ ]] τ₅
                           cps[ τ₅ , τ₄ ]} → 
             {v₂ : value𝑘[ var ] τ₂ ⇒ τ₁ cps[ τ₃ , τ₄ ] cps[τ,τ]} →
             {w₂ : value𝑘[ var ] τ₂ cps[τ,τ]} →
             SubstCon𝑘 k₁ v K𝑐 k₂ → SubstValV𝑘 v₁ v v₂ → SubstValV𝑘 w₁ v w₂ → 
             Subst𝑘 (λ y k′  → NonVal (k₁ y k′) (App (v₁ y) (w₁ y)))
                    v K𝑐
                    (NonVal k₂ (App v₂ w₂))
    sReset : {τ τ₁ τ₂ τ₃ τ₄ τ₅ α β γ ε ζ : typ𝑘} →
             {k₁ : var τ → var (α ⇒ ε cps[ β , ζ ]) → 
                   pcontext𝑘[ var , τ₂ cps[ τ₃ , τ₃ ]] τ₅
                           cps[ τ₅ , τ₃ ]} →
             {e₁ : var τ → var (α ⇒ ε cps[ β , ζ ]) → term𝑘[ var ] τ₁ cps[ τ₁ , τ₂ ]} → 
             {v  : value𝑘[ var ] τ cps[τ,τ]} →
             {K𝑐 : pcontext𝑘[ var , α cps[ β , γ ]] ε cps[ ζ , γ ]} → 
             {k₂ : pcontext𝑘[ var , τ₂ cps[ τ₃ , τ₃ ]] τ₅
                           cps[ τ₅ , τ₃ ]} →
             {e₂ : term𝑘[ var ] τ₁ cps[ τ₁ , τ₂ ]} →
             SubstCon𝑘 k₁ v K𝑐 k₂ → Subst𝑘 e₁ v K𝑐 e₂ → 
             Subst𝑘 (λ y k′ → NonVal (k₁ y k′) (Reset τ₁ τ₂ τ₃ (e₁ y k′)))
                    v K𝑐 
                    (NonVal k₂ (Reset τ₁ τ₂ τ₃ e₂))

data ReduceRoot𝑘 {var : typ𝑘 → Set} :
                 {τ₁ τ₂ τ₃ : typ𝑘} →
                 root𝑘[ var ] τ₁ cps[ τ₂ , τ₃ ] →
                 root𝑘[ var ] τ₁ cps[ τ₂ , τ₃ ] → Set where
     βVal  : {τ τ₁ τ₂ τ₃ τ₄ : typ𝑘} →
              {K𝑐 : pcontext𝑘[ var , τ₁ cps[ τ₃ , τ₄ ]] τ₃ cps[ τ₃ , τ₄ ]} →
              {e  : var τ₂ → var (τ₁ ⇒ τ₃ cps[ τ₃ , τ₃ ]) →
                    term𝑘[ var ] τ₃ cps[ τ₃ , τ₄ ]} →
              {v  : value𝑘[ var ] τ₂ cps[τ,τ]} →
              {e′ : term𝑘[ var ] τ₃ cps[ τ₃ , τ₄ ]} →
              Subst𝑘 e v K𝑐 e′ → 
              ReduceRoot𝑘 {τ₁ = τ}
                (Root (λ k → NonVal K𝑐 (App (Fun τ₁ τ₂ (λ x → Root λ k′ → e x k′))
                                            v)))
                          (Root (λ k → e′))

data ReduceTerm𝑘 {var : typ𝑘 → Set} :
                 {τ₂ τ₃ : typ𝑘} →
                 term𝑘[ var ] τ₂ cps[ τ₂ , τ₃ ] →
                 term𝑘[ var ] τ₂ cps[ τ₂ , τ₃ ] → Set where
     βLet : {τ₁ τ₂ β : typ𝑘} →
             {e₂  : var τ₁ → term𝑘[ var ] τ₂ cps[ τ₂ , β ]} →
             {v   : value𝑘[ var ] τ₁ cps[τ,τ]} →
             {e₂′ : term𝑘[ var ] τ₂ cps[ τ₂ , β ]} →
             SubstV𝑘 (λ x → e₂ x) v e₂′ → 
             ReduceTerm𝑘 (Val (Frame (Let e₂) Hole) v) e₂′

     βShift : {τ τ₁ τ₂ τ₃ τ₄ τ₅ : typ𝑘} →
               {K𝑐 : pcontext𝑘[ var , τ₃ cps[ τ₄ , τ₄ ]] τ₅ cps[ τ₅ , τ₄ ]} →
               {w : value𝑘[ var ] (τ₃ ⇒ τ₄ cps[ τ , τ ]) ⇒ τ₁ cps[ τ₁ , τ₄ ] cps[τ,τ]} → 
               ReduceTerm𝑘 (NonVal Hole (Reset τ₅ τ₄ τ₄
                 (NonVal K𝑐
                 (App Shift w))))
                           (NonVal Hole (Reset τ₁ τ₄ τ₄
                 (NonVal Hole
                 (App w
                      (Fun τ₄ τ₃
                      (λ y → Root (λ k → NonVal (Frame (App₂ k) Hole)
                             (Reset τ₅ τ₄ τ (Val K𝑐 (Var y))))))))))

     -- RShift : {τ τ₁ τ₂ τ₃ τ₄ τ₅ τ₆ τ₇ τ₈ τ₉ : typ𝑘} →
     --          {k : pcontext𝑘[ var , τ₂ cps[ τ₆ , τ₆ ]] τ₇ cps[ τ₈ , τ₉ ] } →
     --          {v₂ : value𝑘[ var ] (τ₃ ⇒ τ₃ cps[ τ , τ ]) ⇒ τ₁ cps[ τ₁ , τ₂ ] cps[τ,τ] } →
     --          {p₁ : pcontext𝑘[ var , τ₃ cps[ τ₃ , τ₂ ]] τ₅ cps[ τ₅ , τ₂ ] } →
     --          {p₂ : pcontext𝑘[ var , τ₃ cps[ τ₃ , τ₃ ]] τ₅ cps[ τ₅ , τ₃ ] } →
     --          same-pcontext𝑘 p₁ p₂ → 
     --          Reduce𝑘 (NonVal k (Reset τ₃ τ₅ τ₂ τ₆
     --                                   (NonVal p₁ (App Shift v₂))))
     --                  (NonVal k (Reset τ₁ τ₁ τ₂ τ₆
     --                                   (NonVal Hole (App v₂ (Fun τ₃ τ₃ (λ y →
     --                                                        NonVal Hole (Reset τ₃ τ₅ τ₃ τ
     --                                                                           (Val p₂ (Var y)))))))))

data ReduceVal𝑘 {var : typ𝑘 → Set} :
                 {τ₁ : typ𝑘} →
                 value𝑘[ var ] τ₁ cps[τ,τ] →
                 value𝑘[ var ] τ₁ cps[τ,τ] → Set where
     ηVal : {τ₁ τ₂ τ₃ τ₄ : typ𝑘} →
             {v : value𝑘[ var ] τ₂ ⇒ τ₁ cps[ τ₃ , τ₄ ] cps[τ,τ]} →
             ReduceVal𝑘 (Fun τ₁ τ₂ (λ x → Root (λ k →
                             NonVal (Frame (App₂ k) Hole) (App v (Var x)))))
                        v

data ReduceCon𝑘 {var : typ𝑘 → Set} :
                {τ₁ τ₂ τ₃ τ₇ : typ𝑘} →
                 pcontext𝑘[ var , τ₁ cps[ τ₂ , τ₃ ]] τ₇ cps[ τ₇ , τ₃ ] →
                 pcontext𝑘[ var , τ₁ cps[ τ₂ , τ₃ ]] τ₇ cps[ τ₇ , τ₃ ] → Set where
     ηLet : {τ₁ τ₂ β : typ𝑘} →
             {K𝑐 : pcontext𝑘[ var , τ₁ cps[ β , β ]] τ₂ cps[ τ₂ , β ]} → 
             ReduceCon𝑘 (Frame (Let (λ x → Val K𝑐 (Var x))) Hole)
                        K𝑐
