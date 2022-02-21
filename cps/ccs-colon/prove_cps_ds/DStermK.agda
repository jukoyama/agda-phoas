module DStermK where

open import Data.Nat

-- type
data typ𝑘 : Set where
  Nat          : typ𝑘
  Boolean      : typ𝑘
  _⇒_cps[_,_]  : typ𝑘 → typ𝑘 → typ𝑘 → typ𝑘 → typ𝑘
  _▷_          : typ𝑘 → typ𝑘 → typ𝑘

-- source kernel term
mutual
  data value𝑘[_]_cps[τ,τ] (var : typ𝑘 → Set) : typ𝑘 → Set where
    Num   : ℕ → value𝑘[ var ] Nat cps[τ,τ]
    Var   : {τ₁ : typ𝑘} → var τ₁ → value𝑘[ var ] τ₁ cps[τ,τ]
    Fun   : {τ₀ τ₁ τ₃ τ₄ : typ𝑘} →
            (var τ₀ → var (τ₁ ▷ τ₃) → term𝑘[ var ] τ₄) →
            value𝑘[ var ] (τ₀ ⇒ τ₁ cps[ τ₃ , τ₄ ]) cps[τ,τ]
    Shift : {τ τ₁ τ₂ τ₃ τ₄ : typ𝑘} →
            value𝑘[ var ]
             (((τ₃ ⇒ τ₄ cps[ τ , τ ]) ⇒ τ₁ cps[ τ₁ , τ₂ ])
               ⇒ τ₃ cps[ τ₄ , τ₂ ])
               cps[τ,τ]

  data term𝑘[_]_ (var : typ𝑘 → Set) : typ𝑘 → Set where
    Ret  : {τ₁ τ₂ : typ𝑘} →
           pcontext𝑘[ var ] τ₁ ▷ τ₂ →
           value𝑘[ var ] τ₁ cps[τ,τ] →
           term𝑘[ var ] τ₂
    App  : {τ₁ τ₂ τ₃ τ₄ : typ𝑘} →
           value𝑘[ var ] τ₂ ⇒ τ₁ cps[ τ₃ , τ₄ ] cps[τ,τ] →
           value𝑘[ var ] τ₂ cps[τ,τ] → 
           pcontext𝑘[ var ] τ₁ ▷ τ₃ →
           term𝑘[ var ] τ₄
    RetE : {τ₁ τ₂ : typ𝑘} →
           pcontext𝑘[ var ] τ₁ ▷ τ₂ →
           term𝑘[ var ] τ₁ →
           term𝑘[ var ] τ₂

  data pcontext𝑘[_]_▷_ (var : typ𝑘 → Set) : typ𝑘 → typ𝑘 → Set where
    KHole : {τ₁ τ₂ : typ𝑘} →
            var (τ₁ ▷ τ₂) →
            pcontext𝑘[ var ] τ₁ ▷ τ₂
    Hole  : {τ₁ : typ𝑘} →
            pcontext𝑘[ var ] τ₁ ▷ τ₁
    KLet  : {τ₁ τ₂ : typ𝑘} →
            (e₂ : var τ₁ → term𝑘[ var ] τ₂) →
            pcontext𝑘[ var ] τ₁ ▷ τ₂

mutual
  data SubstValV𝑘 {var : typ𝑘 → Set} : {τ τ₁ : typ𝑘} →
                  (var τ → value𝑘[ var ] τ₁ cps[τ,τ]) →
                  value𝑘[ var ] τ cps[τ,τ] →
                  value𝑘[ var ] τ₁ cps[τ,τ] → Set where
    sVar=  : {τ : typ𝑘} {v : value𝑘[ var ] τ cps[τ,τ]} →
             SubstValV𝑘 (λ x → Var x) v v
    sVar≠  : {τ τ₁ : typ𝑘} {v : value𝑘[ var ] τ cps[τ,τ]} {x : var τ₁} →
             SubstValV𝑘 (λ _ → Var x) v (Var x)
    sNum   : {τ : typ𝑘} {v : value𝑘[ var ] τ cps[τ,τ]} {n : ℕ} →
             SubstValV𝑘 (λ _ → Num n) v (Num n)
    sShift : {τ₀ τ τ₁ τ₂ τ₃ τ₄ : typ𝑘} {v : value𝑘[ var ] τ₀ cps[τ,τ]} →
             SubstValV𝑘 (λ _ → Shift {τ = τ} {τ₁} {τ₂} {τ₃} {τ₄}) v Shift
    sFun   : {τ′ τ₀ τ₁ τ₃ τ₄ : typ𝑘} →
             {e₁  : var τ′ → var τ₀ → var (τ₁ ▷ τ₃) → 
                    term𝑘[ var ] τ₄} →
             {v   : value𝑘[ var ] τ′ cps[τ,τ]} →
             {e₁′ : var τ₀ → var (τ₁ ▷ τ₃) →
                    term𝑘[ var ] τ₄} →
             ((x : var τ₀) → (k : var (τ₁ ▷ τ₃)) →
              SubstV𝑘 (λ y → (e₁ y) x k) v (e₁′ x k)) →
             SubstValV𝑘 (λ y → Fun (λ x k → e₁ y x k))
                        v
                        (Fun e₁′)

  data SubstConV𝑘 {var : typ𝑘 → Set} : {τ τ₁ τ₂ : typ𝑘} →
                  (var τ → pcontext𝑘[ var ] τ₁ ▷ τ₂) →
                  value𝑘[ var ] τ cps[τ,τ] →
                  pcontext𝑘[ var ] τ₁ ▷ τ₂ → Set where
    sConVar≠ : {τ τ₁ τ₂ : typ𝑘} →
               {k′ : var (τ₁ ▷ τ₂)} → 
               {v : value𝑘[ var ] τ cps[τ,τ]} →
               SubstConV𝑘 (λ _ → KHole k′) v (KHole k′)
    sConId   : {τ τ₁ : typ𝑘} →
               {v : value𝑘[ var ] τ cps[τ,τ]} →
               SubstConV𝑘 {τ₁ = τ₁} (λ _ → Hole) v Hole 
    sConLet  : {τ τ₁ τ₂ : typ𝑘} →
               {e₁ : var τ → var τ₁ → term𝑘[ var ] τ₂} →  
               {v  : value𝑘[ var ] τ cps[τ,τ]}→
               {e₂ : var τ₁ → term𝑘[ var ] τ₂} →
               ((x : var τ₁) → SubstV𝑘 (λ y → (e₁ y) x) v (e₂ x)) → 
               SubstConV𝑘 (λ y → KLet (λ x → (e₁ y) x))
                          v
                          (KLet (λ x → e₂ x)) 

  data SubstV𝑘 {var : typ𝑘 → Set} : {τ₁ τ₂ : typ𝑘} →
               (var τ₁ → term𝑘[ var ] τ₂) →
               value𝑘[ var ] τ₁ cps[τ,τ] →
               term𝑘[ var ] τ₂ → Set where
  　-- sRet にあとで改名
    sVal   : {τ τ₁ τ₂ : typ𝑘} →
             {k₁ : var τ →
                   pcontext𝑘[ var ] τ₁ ▷ τ₂} →
             {v₁ : var τ → value𝑘[ var ] τ₁ cps[τ,τ]} → 
             {v : value𝑘[ var ] τ cps[τ,τ]} →
             {k₂ : pcontext𝑘[ var ] τ₁ ▷ τ₂} →
             {v₂ : value𝑘[ var ] τ₁ cps[τ,τ]} →
             SubstConV𝑘 k₁ v k₂ → SubstValV𝑘 v₁ v v₂ →
             SubstV𝑘 (λ y → Ret (k₁ y) (v₁ y)) v (Ret k₂ v₂)
    sApp   : {τ τ₁ τ₂ τ₃ τ₄ : typ𝑘} →
             {k₁ : var τ → pcontext𝑘[ var ] τ₁ ▷ τ₃} → 
             {v₁ : var τ → value𝑘[ var ] τ₂ ⇒ τ₁ cps[ τ₃ , τ₄ ] cps[τ,τ]} →
             {w₁ : var τ → value𝑘[ var ] τ₂ cps[τ,τ]} →
             {v  : value𝑘[ var ] τ cps[τ,τ]} →
             {k₂ : pcontext𝑘[ var ] τ₁ ▷ τ₃} → 
             {v₂ : value𝑘[ var ] τ₂ ⇒ τ₁ cps[ τ₃ , τ₄ ] cps[τ,τ]} →
             {w₂ : value𝑘[ var ] τ₂ cps[τ,τ]} →
             SubstConV𝑘 k₁ v k₂ → SubstValV𝑘 v₁ v v₂ → SubstValV𝑘 w₁ v w₂ → 
             SubstV𝑘 (λ y → (App (v₁ y) (w₁ y) (k₁ y)))
                    v
                    (App v₂ w₂ k₂)
    -- sRetE にあとで改名
    sReset : {τ τ₁ τ₂ : typ𝑘} →
             {k₁ : var τ → pcontext𝑘[ var ] τ₁ ▷ τ₂} →
             {e₁ : var τ → term𝑘[ var ] τ₁} → 
             {v  : value𝑘[ var ] τ cps[τ,τ]} →
             {k₂ : pcontext𝑘[ var ] τ₁ ▷ τ₂} →
             {e₂ : term𝑘[ var ] τ₁} →
             SubstConV𝑘 k₁ v k₂ → SubstV𝑘 e₁ v e₂ → 
             SubstV𝑘 (λ y → (RetE (k₁ y) (e₁ y)))
                     v
                     (RetE k₂ e₂)

mutual
  data SubstCon𝑘 {var : typ𝑘 → Set} : {τ τ₁ τ₂ α β : typ𝑘} →
                 (var τ → var (α ▷ β) → pcontext𝑘[ var ] τ₁ ▷ τ₂) →
                 value𝑘[ var ] τ cps[τ,τ] →
                 pcontext𝑘[ var ] α ▷ β →
                 pcontext𝑘[ var ] τ₁ ▷ τ₂ → Set where
    sCon= : {τ α β : typ𝑘} →
            {v  : value𝑘[ var ] τ cps[τ,τ]} → 
            {K𝑐 : pcontext𝑘[ var ] α ▷ β} →
            SubstCon𝑘 (λ _ k → KHole k) v K𝑐 K𝑐
    sCon≠ : {τ τ₁ τ₂ α β : typ𝑘} →
            {v  : value𝑘[ var ] τ cps[τ,τ]} → 
            {K𝑐 : pcontext𝑘[ var ] α ▷ β} →
            {k′ : var (τ₁ ▷ τ₂)} → 
            SubstCon𝑘 (λ _ _ → KHole k′) v K𝑐 (KHole k′)
    sHole : {τ τ₁ α β : typ𝑘} →
            {v  : value𝑘[ var ] τ cps[τ,τ]} → 
            {K𝑐 : pcontext𝑘[ var ] α ▷ β} → 
            SubstCon𝑘 {τ₁ = τ₁} (λ _ _ → Hole) v K𝑐 Hole
    sLet  : {τ τ₁ τ₂ α β : typ𝑘} →            
            {e  : var τ → var (α ▷ β) →
                  (var τ₁ → term𝑘[ var ] τ₂)} →
            {v  : value𝑘[ var ] τ cps[τ,τ]} → 
            {K𝑐 : pcontext𝑘[ var ] α ▷ β} →
            {e′ : var τ₁ → term𝑘[ var ] τ₂} →
            ((x : var τ₁) → Subst𝑘 (λ y k′ → (e y k′) x) v K𝑐 (e′ x)) → 
            SubstCon𝑘 (λ y k′ → KLet (e y k′))
                                 v K𝑐
                                 (KLet e′)

  data Subst𝑘 {var : typ𝑘 → Set} : {τ τ₁ α β : typ𝑘} →
              (var τ → var (α ▷ β) → term𝑘[ var ] τ₁) →
              value𝑘[ var ] τ cps[τ,τ] →
              pcontext𝑘[ var ] α ▷ β → 
              term𝑘[ var ] τ₁ → Set where
    -- sRet にあとで改名
    sVal  : {τ τ₁ τ₂ α β : typ𝑘} →
            {k₁ : var τ → var (α ▷ β) → pcontext𝑘[ var ] τ₁ ▷ τ₂} →
            {v₁ : var τ → value𝑘[ var ] τ₁ cps[τ,τ]} →
            {v  : value𝑘[ var ] τ cps[τ,τ]} →
            {K𝑐 : pcontext𝑘[ var ] α ▷ β} →
            {k₂ : pcontext𝑘[ var ] τ₁ ▷ τ₂} →
            {v₂ : value𝑘[ var ] τ₁ cps[τ,τ]} →
            SubstCon𝑘 k₁ v K𝑐 k₂ → SubstValV𝑘 v₁ v v₂ → 
            Subst𝑘 (λ y k′ → Ret (k₁ y k′) (v₁ y)) v K𝑐 (Ret k₂ v₂)
    sApp   : {τ τ₁ τ₂ τ₃ τ₄ α β : typ𝑘} →
             {k₁ : var τ → var (α ▷ β) → pcontext𝑘[ var ] τ₁ ▷ τ₃} → 
             {v₁ : var τ → value𝑘[ var ] τ₂ ⇒ τ₁ cps[ τ₃ , τ₄ ] cps[τ,τ]} →
             {w₁ : var τ → value𝑘[ var ] τ₂ cps[τ,τ]} →
             {v  : value𝑘[ var ] τ cps[τ,τ]} →
             {K𝑐 : pcontext𝑘[ var ] α ▷ β} → 
             {k₂ : pcontext𝑘[ var ] τ₁ ▷ τ₃} → 
             {v₂ : value𝑘[ var ] τ₂ ⇒ τ₁ cps[ τ₃ , τ₄ ] cps[τ,τ]} →
             {w₂ : value𝑘[ var ] τ₂ cps[τ,τ]} →
             SubstCon𝑘 k₁ v K𝑐 k₂ → SubstValV𝑘 v₁ v v₂ → SubstValV𝑘 w₁ v w₂ → 
             Subst𝑘 (λ y k′  → (App (v₁ y) (w₁ y) (k₁ y k′)))
                    v K𝑐
                    (App v₂ w₂ k₂)
    -- sRetE にあとで改名
    sReset : {τ τ₁ τ₂ α β : typ𝑘} →
             {k₁ : var τ → var (α ▷ β) → pcontext𝑘[ var ] τ₁ ▷ τ₂} →
             {e₁ : var τ → var (α ▷ β) → term𝑘[ var ] τ₁} → 
             {v  : value𝑘[ var ] τ cps[τ,τ]} →
             {K𝑐 : pcontext𝑘[ var ] α ▷ β} → 
             {k₂ : pcontext𝑘[ var ] τ₁ ▷ τ₂} →
             {e₂ : term𝑘[ var ] τ₁} →
             SubstCon𝑘 k₁ v K𝑐 k₂ → Subst𝑘 e₁ v K𝑐 e₂ → 
             Subst𝑘 (λ y k′ → (RetE (k₁ y k′) (e₁ y k′)))
                    v K𝑐 
                    (RetE k₂ e₂)

data ReduceTerm𝑘 {var : typ𝑘 → Set} : {τ₁ : typ𝑘} →
                 term𝑘[ var ] τ₁ →
                 term𝑘[ var ] τ₁ → Set where
     βVal : {τ₀ τ₁ τ₃ τ₄ : typ𝑘} →
             {K𝑐 : pcontext𝑘[ var ] τ₁ ▷ τ₃} →
             {e  : var τ₀ → var (τ₁ ▷ τ₃) →
                   term𝑘[ var ] τ₄} →
             {v  : value𝑘[ var ] τ₀ cps[τ,τ]} →
             {e′ : term𝑘[ var ] τ₄} →
             Subst𝑘 e v K𝑐 e′ →
             ReduceTerm𝑘 (App (Fun (λ x k′ → e x k′)) v K𝑐)
                         e′
     βLet : {τ₁ τ₂ : typ𝑘} →
             {e₂  : var τ₁ → term𝑘[ var ] τ₂} →
             {v   : value𝑘[ var ] τ₁ cps[τ,τ]} →
             {e₂′ : term𝑘[ var ] τ₂} →
             SubstV𝑘 (λ x → e₂ x) v e₂′ → 
             ReduceTerm𝑘 (Ret (KLet e₂) v) e₂′

data ReduceTerm𝑘𝑠 {var : typ𝑘 → Set} : {τ₁ : typ𝑘} →
                  term𝑘[ var ] τ₁ →
                  term𝑘[ var ] τ₁ → Set where
     βShift : {τ₁ τ₃ τ₄ : typ𝑘} →
               {J : pcontext𝑘[ var ] τ₃ ▷ τ₄} →
               {w : value𝑘[ var ] (τ₃ ⇒ τ₄ cps[ τ₃ , τ₃ ]) ⇒ τ₁ cps[ τ₁ , τ₄ ] cps[τ,τ]} →
               ReduceTerm𝑘𝑠 (RetE Hole
                                  (App Shift w J))
                            (RetE Hole
                                  (App w (Fun (λ y k → RetE (KHole k) (Ret J (Var y)))) Hole))
                                                                        
data ReduceTerm𝑘𝑅 {var : typ𝑘 → Set} : {τ₂ : typ𝑘} →
                  term𝑘[ var ] τ₂ →
                  value𝑘[ var ] τ₂ cps[τ,τ] → Set where
     βReset : {τ₁ : typ𝑘} →
               {v : value𝑘[ var ] τ₁ cps[τ,τ]} →
               ReduceTerm𝑘𝑅 (RetE Hole (Ret Hole v))
                            v

-- ReduceV𝑘 にあとで改名
data ReduceVal𝑘 {var : typ𝑘 → Set} : {τ₁ : typ𝑘} →
                 value𝑘[ var ] τ₁ cps[τ,τ] →
                 value𝑘[ var ] τ₁ cps[τ,τ] → Set where
     ηVal : {τ₀ τ₁ τ₃ τ₄ : typ𝑘} →
             {v : value𝑘[ var ] τ₀ ⇒ τ₁ cps[ τ₃ , τ₄ ] cps[τ,τ]} →
             ReduceVal𝑘 (Fun (λ x k →
                             (App v (Var x) (KHole k))))
                        v

data ReduceCon𝑘 {var : typ𝑘 → Set} : {τ₁ τ₂ : typ𝑘} →
                 pcontext𝑘[ var ] τ₁ ▷ τ₂ →
                 pcontext𝑘[ var ] τ₁ ▷ τ₂ → Set where
     ηLet : {τ₁ τ₂ : typ𝑘} →
             {K𝑐 : pcontext𝑘[ var ] τ₁ ▷ τ₂} → 
             ReduceCon𝑘 (KLet (λ x → Ret K𝑐 (Var x)))
                        K𝑐
