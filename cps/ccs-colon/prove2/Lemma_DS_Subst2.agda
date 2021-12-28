module Lemma_DS_Subst2 where

open import CPSterm2
open import DStermK2
open import DSTrans2

open import Function

-- 必要がないかも
-- mutual
--   dsSubstValV𝑘≠ : {var : typ𝑘 → Set} {τ₁ τ₂ : typ𝑘} → 
--                   {t : value𝑘[ var ] τ₁ cps[τ,τ]} →
--                   {v : value𝑘[ var ] τ₂ cps[τ,τ]} →
--                   SubstValV𝑘 (λ y → t) v t
--   dsSubstValV𝑘≠ = {!!}

--   dsSubstV𝑘≠ : {var : typ𝑘 → Set} {τ₁ τ₂ τ₃ : typ𝑘} →
--                {t : term𝑘[ var ] τ₂ cps[ τ₂ , τ₃ ]} →
--                {v : value𝑘[ var ] τ₁ cps[τ,τ]} →
--                {!!}
--   dsSubstV𝑘≠ = {!!}

mutual
  eSubstValV𝑘 : {var : typ𝑘 → Set} {τ₁ τ : cpstyp} →
                 {v₁ : var (dsT τ) → cpsvalue𝑐[ var ∘ dsT ] τ₁} →
                 {v₂ : cpsvalue𝑐[ var ∘ dsT ] τ₁} →
                 {v  : cpsvalue𝑐[ var ∘ dsT ] τ} →
                 cpsSubstValV𝑐 v₁ v v₂ →
                 SubstValV𝑘 {var} (λ y → dsV𝑐 τ₁ (v₁ y))
                                  (dsV𝑐 τ v)
                                  (dsV𝑐 τ₁ v₂)
  eSubstValV𝑘 = {!!}  

  -- eSubstConV𝑘 : {var : typ𝑘 → Set} {τ τ₁ τ₂ τ₃ τ₄ : cpstyp} →
  --               {k₁ : var (dsT τ) →
  --                     cpscont𝑐[ var ∘ dsT ] (τ₄ ⇒ τ₄) (τ₁ ⇒ τ₂)} →
  --               {k₂ : cpscont𝑐[ var ∘ dsT ] (τ₄ ⇒ τ₄) (τ₁ ⇒ τ₂)} →
  --               {v  : cpsvalue𝑐[ var ∘ dsT ] τ} →
  --               cpsSubstContV𝑐 k₁ v k₂ →
  --               SubstConV𝑘 {var} (λ y → dsC𝑐 τ₁ τ₂ τ₃ τ₄ (k₁ y))
  --                                (dsV𝑐 τ v)
  --                                (dsC𝑐 τ₁ τ₂ τ₃ τ₄ k₂)
  -- eSubstConV𝑘 = {!!}

  -- eSubstRootV𝑘 : {var : typ𝑘 → Set} {τ τ₂ τ₃ : cpstyp} →
  --                {e₁ : var (dsT τ) →
  --                      cpsterm𝑐[ var ∘ dsT ] (τ₃ ⇒ τ₃) τ₂} →
  --                {e₂ : cpsterm𝑐[ var ∘ dsT ] (τ₃ ⇒ τ₃) τ₂} →
  --                {v  : cpsvalue𝑐[ var ∘ dsT ] τ} →
  --                cpsSubstV𝑐 e₁ v e₂ →
  --                SubstRootV𝑘 (λ y → dsMain𝑐 {!!} {!!} {!!} e₁) {!!} {!!}
  -- eSubstRootV𝑘 = {!!}


  -- eSubstV𝑘 : {var : typ𝑘 → Set} {τ τ₂ τ₃ : cpstyp} →
  --            {e₁ : var (dsT τ) →
  --                  cpsterm𝑐[ var ∘ dsT ] (τ₃ ⇒ τ₃) τ₂} →
  --            {e₂ : cpsterm𝑐[ var ∘ dsT ] (τ₃ ⇒ τ₃) τ₂} →
  --            {v  : cpsvalue𝑐[ var ∘ dsT ] τ} →
  --            cpsSubstV𝑐 e₁ v e₂ →
  --            SubstV𝑘 {var} (λ y → dsE𝑐 τ₂ τ₃ (e₁ y))
  --                          (dsV𝑐 τ v)
  --                          (dsE𝑐 τ₂ τ₃ e₂)
  -- eSubstV𝑘 = {!!}

mutual
  eSubstConVK𝑘 : {var : typ𝑘 → Set} {τ τ₁ τ₂ τ₃ τ₇ α β γ ζ : cpstyp} →
                 {k₁ : var (dsT τ) → var (dsT (α ⇒[ (β ⇒ {!ζ!}) ]⇒ {!!})) →
                       cpscont𝑐[ var ∘ dsT ] (τ₇ ⇒ τ₇) (τ₁ ⇒ τ₂)} →
                 {k₂ : cpscont𝑐[ var ∘ dsT ] (τ₇ ⇒ τ₇) (τ₁ ⇒ τ₂)} →
                 {v  : cpsvalue𝑐[ var ∘ dsT ] τ} →
                 {c : cpscont𝑐[ var ∘ dsT ] ({!!} ⇒ {!!}) (α ⇒ β)} →
                 cpsSubstCont𝑐 k₁ v c k₂ →
                 SubstCon𝑘 {var} (λ y k′ → dsC𝑐 τ₁ τ₂ τ₃ τ₇ (k₁ y k′))
                                 (dsV𝑐 τ v) (dsC𝑐 α β {!!} {!ζ!} c)
                                 (dsC𝑐 τ₁ τ₂ τ₃ τ₇ k₂)
  eSubstConVK𝑘 {var} {τ} {τ₁} {τ₂} {τ₃} {.τ₂} {.τ₁} {.τ₂} {.τ₃} {.τ₂}
               {.(λ _ k → CPSKVar {_} {τ₁} {τ₂} k)}
               {k₂} {v} {.k₂}
               (sKVar= {τ = .τ} {α = .τ₁} {β = .τ₂} {v = .v} {c = .k₂}) =
    sCon=


  eSubstConVK𝑘 {var} {τ} {τ₁} {τ₂} {τ₃} {.τ₂} {α} {β} {γ} {ζ}
               {.(λ _ _ → CPSKVar {_} {τ₁} {τ₂} k′)}
               {.(CPSKVar {_} {τ₁} {τ₂} k′)} {v} {c}
               (sKVar≠ {τ = .τ} {α = .α} {β = .β} {γ = .ζ} {τ₁ = .τ₁} {τ₂ = .τ₂}
                       {v = .v} {c = .c} {k′ = k′}) =
    sCon≠
  eSubstConVK𝑘 {var} {τ} {τ₁} {.τ₁} {τ₃} {.τ₁} {α} {β} {γ} {ζ}
               {.(λ _ _ → CPSId {_} {τ₁})}
               {.(CPSId {_} {τ₁})} {v} {c}
               (sKId {τ = .τ} {α = .α} {β = .β} {γ = .ζ} {τ₁ = .τ₁} {v = .v} {c = .c}) =
    sHole
  eSubstConVK𝑘 {var} {τ} {τ₁} {τ₂} {τ₃} {τ₇} {α} {β} {.τ₃} {ζ}
               {.(λ x₁ k → CPSCont {_} {τ₁} {τ₂} {τ₇} (e₁ x₁ k))}
               {.(CPSCont {_} {τ₁} {τ₂} {τ₇} e₁′)} {v} {c}
               (sKFun {τ = .τ} {τ₁ = .τ₁} {τ₂ = .τ₂} {τ₄ = .τ₇} {α = .α} {β = .β} {γ = .ζ}
                      {e₁ = e₁} {v = .v} {c = .c} {e₁′ = e₁′} sub-e) =
    sLet sub-e

-- TODO : DSkernel との型の名前を一致するべきか
  eSubstVK𝑘 : {var : typ𝑘 → Set} {τ τ₁ τ₃ α β γ ζ  : cpstyp} →
              {e₁ : var (dsT τ) → var (dsT (α ⇒[ (β ⇒ γ) ]⇒ γ)) →
                    cpsterm𝑐[ var ∘ dsT ] (τ₃ ⇒ τ₃) τ₁} →
              {e₂ : cpsterm𝑐[ var ∘ dsT ] (τ₃ ⇒ τ₃) τ₁} →
              {v  : cpsvalue𝑐[ var ∘ dsT ] τ} →
              {c : cpscont𝑐[ var ∘ dsT ] (γ ⇒ γ) (α ⇒ β)} →
              cpsSubst𝑐 e₁ v c e₂ → 
              Subst𝑘 {var} (λ y k′ → dsE𝑐 τ₁ τ₃ (e₁ y k′))
                           (dsV𝑐 τ v) (dsC𝑐 α β ζ γ c)
                           (dsE𝑐 τ₁ τ₃ e₂)
  eSubstVK𝑘 (sApp sub-v sub-w sub-k) = sApp (eSubstConVK𝑘 sub-k)
                                            (eSubstValV𝑘 sub-v)
                                            (eSubstValV𝑘 sub-w)
  eSubstVK𝑘 (sRet sub-k sub-v)       = sVal (eSubstConVK𝑘 sub-k)
                                            (eSubstValV𝑘 sub-v)
  eSubstVK𝑘 (sRetE sub-k sub-e)      = sReset (eSubstConVK𝑘 sub-k)
                                              (eSubstVK𝑘 sub-e)

