module DStermK where

open import DSterm

open import Data.Nat

-- source kernel term
mutual
  data value𝑘[_]_cps[τ,τ] (var : typ → Set) : typ → Set where
    Num   : ℕ → value𝑘[ var ] Nat cps[τ,τ]
    Var   : {τ₁ : typ} → var τ₁ → value𝑘[ var ] τ₁ cps[τ,τ]
    Fun   : (τ₁ τ₂ {τ₃ τ₄} : typ) →
            (var τ₂ → term𝑘[ var ] τ₁ cps[ τ₃ , τ₄ ]) →
            value𝑘[ var ] (τ₂ ⇒ τ₁ cps[ τ₃ , τ₄ ]) cps[τ,τ]
    Shift : {τ τ₁ τ₂ τ₃ τ₄ : typ} →
            value𝑘[ var ]
             (((τ₃ ⇒ τ₄ cps[ τ , τ ]) ⇒ τ₁ cps[ τ₁ , τ₂ ])
               ⇒ τ₃ cps[ τ₄ , τ₂ ])
               cps[τ,τ]

  data term𝑘[_]_cps[_,_] (var : typ → Set) : typ → typ → typ → Set where
    Val    : {τ₁ τ₂ : typ} →
             term𝑘[ var ] {!!} cps[ {!!} , {!!} ]
    NonVal : {τ₁ τ₂ τ₃ : typ} →
             nonvalue𝑘[ var ] τ₁ cps[ τ₂ , τ₃ ] →
             term𝑘[ var ] τ₁ cps[ τ₂ , τ₃ ]

  data nonvalue𝑘[_]_cps[_,_] (var : typ → Set) : typ → typ → typ → Set where
    App   : {τ₁ τ₂ τ₃ τ₄ : typ} →
            value𝑘[ var ] τ₂ ⇒ τ₁ cps[ τ₃ , τ₄ ] cps[τ,τ] →
            value𝑘[ var ] τ₂ cps[τ,τ] → 
            nonvalue𝑘[ var ] τ₁ cps[ {!!} , {!!} ]
    Reset : (τ₁ τ₂ τ₃ : typ) →
            term𝑘[ var ] τ₁ cps[ τ₁ , τ₂ ] →
            nonvalue𝑘[ var ] τ₂ cps[ τ₃ , τ₃ ]

-- pure frame
data pframe𝑘[_,_cps[_,_]]_cps[_,_] (var : typ → Set)
     : typ → typ → typ → typ → typ → typ → Set where
  Let  : {τ₁ τ₂ α β γ : typ} →
         (e₂ : var τ₁ → term𝑘[ var ] τ₂ cps[ α , β ]) →
         pframe𝑘[ var , τ₁ cps[ β , γ ]] τ₂ cps[ α , γ ]

pframe-plug𝑘 : {var : typ → Set}
               {τ₁ τ₂ τ₃ τ₄ τ₅ τ₆ : typ} →
               pframe𝑘[ var , τ₁ cps[ τ₂ , τ₃ ]] τ₄ cps[ τ₅ , τ₆ ] →
               term𝑘[ var ] τ₁ cps[ τ₂ , τ₃ ] →
               term𝑘[ var ] τ₄ cps[ τ₅ , τ₆ ]
pframe-plug𝑘 (Let e₂)  e₁ = NonVal {!!}


-- pure context
data pcontext𝑘[_,_cps[_,_]]_cps[_,_] (var : typ → Set)
     : typ → typ → typ → typ → typ → typ  → Set where
  Hole  : {τ₁ τ₂ τ₃ : typ} →
          pcontext𝑘[ var , τ₁ cps[ τ₂ , τ₃ ]] τ₁ cps[ τ₂ , τ₃ ]
  Frame : {τ₁ τ₂ τ₃ τ₄ τ₅ τ₆ τ₇ τ₈ τ₉ : typ} →
          (f : pframe𝑘[ var , τ₄ cps[ τ₅ , τ₆ ]] τ₇
                     cps[ τ₈ , τ₉ ]) →
          (e : pcontext𝑘[ var , τ₁ cps[ τ₂ , τ₃ ]] τ₄
                       cps[ τ₅ , τ₆ ]) →
          pcontext𝑘[ var , τ₁ cps[ τ₂ , τ₃ ]] τ₇ cps[ τ₈ , τ₉ ]

pcontext-plug𝑘 : {var : typ → Set}
                {τ₁ τ₂ τ₃ τ₄ τ₅ τ₆ : typ} →
                pcontext𝑘[ var , τ₁ cps[ τ₂ , τ₃ ]] τ₄
                        cps[ τ₅ , τ₆ ] →
                term𝑘[ var ] τ₁ cps[ τ₂ , τ₃ ] →
                term𝑘[ var ] τ₄ cps[ τ₅ , τ₆ ]
pcontext-plug𝑘 Hole        e₁ = e₁
pcontext-plug𝑘 (Frame f p) e₁ = pframe-plug𝑘 f (pcontext-plug𝑘 p e₁)
