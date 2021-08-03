module DStermK where

open import Data.Nat

-- type
data typ𝑘 : Set where
  Nat          : typ𝑘
  Boolean      : typ𝑘
  _⇒_cps[_,_]  : typ𝑘 → typ𝑘 → typ𝑘 → typ𝑘 → typ𝑘

data typ𝑘𝑐 : Set where
  _⇒_cps[_] : typ𝑘 → typ𝑘 → typ𝑘 → typ𝑘𝑐

kerT : typ𝑘𝑐 → typ𝑘
kerT (τ₁ ⇒ τ₂ cps[ τ ]) = τ₁ ⇒ τ₂ cps[ τ , τ ]

-- source kernel term
mutual

  data root𝑘[_]_cps[_,_] (var : typ𝑘 → Set) : typ𝑘 → typ𝑘 → typ𝑘 → Set where
    Root : {τ τ₁ τ₃ τ₄ : typ𝑘} →
           (v₁ : value𝑘[ var ]
             (((τ₁ ⇒ τ₃ cps[ τ , τ ]) ⇒ τ₃ cps[ τ₃ , τ₄ ])
               ⇒ τ₁ cps[ τ₃ , τ₄ ]) cps[τ,τ]) →
           (v₂ : var (τ₁ ⇒ τ₃ cps[ τ , τ ]) → nonvalue𝑘[ var ] τ₃ cps[ τ₃ , τ₄ ]) →
           root𝑘[ var ] τ₁ cps[ τ₃ , τ₄ ]
           
  data value𝑘[_]_cps[τ,τ] (var : typ𝑘 → Set) : typ𝑘 → Set where
    Num   : ℕ → value𝑘[ var ] Nat cps[τ,τ]
    Var   : {τ₁ : typ𝑘} → var τ₁ → value𝑘[ var ] τ₁ cps[τ,τ]
    Fun   : (τ τ₁ τ₂ {τ₃ τ₄} : typ𝑘) →
            (var τ₂ → var (kerT (τ₁ ⇒ τ₃ cps[ τ ])) → term𝑘[ var ] τ₃ cps[ τ₃ , τ₄ ]) → 
            -- (var τ₂ → var (τ₁ ⇒ τ₃ cps[ τ , τ ]) → term𝑘[ var ] τ₃ cps[ τ₃ , τ₄ ]) → 
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
    -- App₂ : {τ₁ τ₂ τ₃ τ₄ τ₅ : typ𝑘} →
    --        (v₁ : value𝑘[ var ] (τ₂ ⇒ τ₁ cps[ τ₃ , τ₄ ]) cps[τ,τ]) →
    --        pframe𝑘[ var , τ₂ cps[ τ₄ , τ₅ ]] τ₁ cps[ τ₃ , τ₅ ]
    App₂ : {τ₁ τ₂ τ₃ τ₅ : typ𝑘} →
           (v₁ : var (τ₂ ⇒ τ₁ cps[ τ₃ , τ₃ ])) →
           pframe𝑘[ var , τ₂ cps[ τ₃ , τ₅ ]] τ₁ cps[ τ₃ , τ₅ ]
    Let  : {τ₁ τ₂ α β γ : typ𝑘} →
           (e₂ : var τ₁ → term𝑘[ var ] τ₂ cps[ α , β ]) →
           pframe𝑘[ var , τ₁ cps[ β , γ ]] τ₂ cps[ α , γ ]
    -- Let  : {τ₁ τ₂ β γ : typ𝑘} →
    --        (e₂ : var τ₁ → term𝑘[ var ] τ₂ cps[ τ₂ , β ]) →
    --        pframe𝑘[ var , τ₁ cps[ β , γ ]] τ₂ cps[ τ₂ , γ ]

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
    Hole  : {τ₁ τ₂ τ₃ : typ𝑘} →
            pcontext𝑘[ var , τ₁ cps[ τ₂ , τ₃ ]] τ₁ cps[ τ₂ , τ₃ ]
    Frame : {τ τ₁ τ₂ τ₇ τ₈ : typ𝑘} →
            (f : pframe𝑘[ var , τ₁ cps[ τ₂ , τ ]] τ₇
                     cps[ τ₈ , τ ]) →
            (e : pcontext𝑘[ var , τ₁ cps[ τ₂ , τ ]] τ₁
                       cps[ τ₂ , τ ]) →
            pcontext𝑘[ var , τ₁ cps[ τ₂ , τ ]] τ₇ cps[ τ₈ , τ ]

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
--   data SubstVal𝑘 {var : typ𝑘 → Set} : {τ₁ τ₂ : typ𝑘} →
--                  (var τ₁ → value𝑘[ var ] τ₂ cps[τ,τ]) →
--                  value𝑘[ var ] τ₁ cps[τ,τ] →
--                  value𝑘[ var ] τ₂ cps[τ,τ] → Set where

--   data Subst𝑘 {var : typ𝑘 → Set} : {τ₁ τ₂ τ₃ τ₄ α β : typ𝑘} →
--               (var τ₁ → term𝑘[ var ] τ₂ cps[ τ₃ , τ₄ ] (α ⇒ β cps[τ,τ])) →
--               value𝑘[ var ] τ₁ cps[τ,τ] →
--               term𝑘[ var ] τ₂ cps[ τ₃ , τ₄ ] (α ⇒ β cps[τ,τ]) → Set where


-- data Reduce𝑘 {var : typ𝑘 → Set} :
--              {τ₁ τ₂ τ₃ α β : typ𝑘} →
--              term𝑘[ var ] τ₁ cps[ τ₂ , τ₃ ] (α ⇒ β cps[τ,τ]) →
--              term𝑘[ var ] τ₁ cps[ τ₂ , τ₃ ] (α ⇒ β cps[τ,τ]) → Set where
--      RBeta  : {τ τ₁ τ₂ τ₃ : typ𝑘} →
--               {k  : pcontext𝑘[ var , τ₁ cps[ τ₂ , τ₃ ]] τ₁ cps[ τ₂ , τ₃ ]} → 
--               {e  : var τ → term𝑘[ var ] τ₁ cps[ τ₂ , τ₃ ] (τ₁ ⇒ τ₂ cps[τ,τ])} →
--               {v  : value𝑘[ var ] τ cps[τ,τ]} → 
--               {e′ : term𝑘[ var ] τ₁ cps[ τ₂ , τ₃ ] (τ₁ ⇒ τ₂ cps[τ,τ])} → 
--               Reduce𝑘 (NonVal k (App (Fun τ₁ τ e) v)) e′
--      RLet   : {τ₁ τ₂ α β : typ𝑘} →
--               {v₁  : value𝑘[ var ] τ₁ cps[τ,τ]} →
--               {e₂  : var τ₁ → term𝑘[ var ] τ₂ cps[ α , β ] (τ₂ ⇒ α cps[τ,τ])} →
--               {e₂′ : term𝑘[ var ] τ₂ cps[ α , β ] (τ₁ ⇒ β cps[τ,τ])} → 
--               Reduce𝑘 (Val (Frame (Let e₂) Hole) v₁) e₂′
--      RShift : {τ τ₁ τ₂ τ₃ τ₄ τ₅ τ₆ τ₇ τ₈ τ₉ : typ𝑘} →
--               {k : pcontext𝑘[ var , τ₂ cps[ τ₆ , τ₆ ]] τ₇ cps[ τ₈ , τ₉ ] } →
--               {v₂ : value𝑘[ var ] (τ₃ ⇒ τ₃ cps[ τ , τ ]) ⇒ τ₁ cps[ τ₁ , τ₂ ] cps[τ,τ] } →
--               {p₁ : pcontext𝑘[ var , τ₃ cps[ τ₃ , τ₂ ]] τ₅ cps[ τ₅ , τ₂ ] } →
--               {p₂ : pcontext𝑘[ var , τ₃ cps[ τ₃ , τ₃ ]] τ₅ cps[ τ₅ , τ₃ ] } →
--               same-pcontext𝑘 p₁ p₂ → 
--               Reduce𝑘 (NonVal k (Reset τ₃ τ₅ τ₂ τ₆
--                                        (NonVal p₁ (App Shift v₂))))
--                       (NonVal k (Reset τ₁ τ₁ τ₂ τ₆
--                                        (NonVal Hole (App v₂ (Fun τ₃ τ₃ (λ y →
--                                                             NonVal Hole (Reset τ₃ τ₅ τ₃ τ
--                                                                                (Val p₂ (Var y)))))))))
