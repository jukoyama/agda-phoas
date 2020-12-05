module lemma1 where

open import DSterm2
open import CPSterm

open import Function

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

eqsubst-cont : {var : cpstyp → Set} {τ₁ τ₂ : typ} {τ₄ : cpstyp} →
               (κ : cpsvalue[ var ] (cpsT τ₁) → cpsterm[ var ] (cpsT τ₂)) →
               (v : cpsvalue[ var ] τ₄) → Set 
eqsubst-cont {var} {τ₁} {τ₂} {τ₄} κ v =
  {v′ : cpsvalue[ var ] (cpsT τ₁)} →
  cpsSubst (λ y → κ v′) v (κ v′)

mutual
  SubstV≠ : {var : cpstyp → Set} {τ₁ τ₂ : cpstyp} →
            {t : cpsvalue[ var ] τ₁} →
            {v : cpsvalue[ var ] τ₂} →
            cpsSubstVal (λ y → t) v t
  SubstV≠ {t = CPSVar x}  = sVar≠
  SubstV≠ {t = CPSNum n}  = sNum
  SubstV≠ {t = CPSFun e₁} = sFun (λ x → Subst≠)
  SubstV≠ {t = CPSShift}  = sShift

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
  eSubstV SubstVal.sShift =
    sFun (λ w → sVal (sFun (λ k →
      sApp (sApp Subst≠ (sVal (sFun (λ a → sVal (sFun (λ k′ → sApp Subst≠ Subst≠)))))) Subst≠)))
  eSubstV (SubstVal.sFun sub) =
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
  eκSubst (sReset sub) eq = sLet (λ c → eq sVar≠) (λ c → eκSubst sub (λ m → sVal m))
  eκSubst (sLet sub₂ sub₁) eq = eκSubst sub₁ λ m → sLet (λ c → eκSubst (sub₂ c) eq) (λ c → sVal m)
     
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
  ekSubst′ k (sApp sub₁ sub₂)  = eκSubst sub₁
                                        (λ m → eκSubst sub₂
                                        (λ n → sApp (sApp (sVal m) (sVal n)) (sVal sVar≠)))
  ekSubst′ k (sReset sub) = sLet (λ c → sApp (sVal sVar≠) (sVal sVar≠))
                                 (λ c → eκSubst sub (λ m → sVal m))
  ekSubst′ k (sLet sub₂ sub₁) = eκSubst sub₁
                                 (λ m → sLet (λ c → ekSubst′ k (sub₂ c))
                                 (λ c → sVal m))

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
eSubst (sReset sub) eq = sLet (λ c → eq sVar≠) (λ c → eSubst sub (λ m → sVal m))
eSubst (sLet sub₂ sub₁) eq =
  eκSubst sub₁ (λ m → sLet (λ c → eκSubst (sub₂ c) eq) (λ c → sVal m))

{----------------SCHEMATIC----------------}

schematic : {var : cpstyp → Set} {τ₁ τ₂ : typ} →
            (κ : cpsvalue[ var ] (cpsT τ₁) →
                  cpsterm[ var ] (cpsT τ₂)) → Set
schematic {var} {τ₁} κ =
  (v : cpsvalue[ var ] (cpsT τ₁)) →
  cpsSubst (λ y → κ (CPSVar y)) v (κ v)

schematic′ : {var : cpstyp → Set} {τ₁ τ₂ : typ} {τ : cpstyp} → -- 
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
         {v : cpsvalue[ var ] τ} → 
         (κ : cpsvalue[ var ] τ →
              cpsvalue[ var ] (cpsT τ₁) → cpsterm[ var ] (cpsT τ₂)) →
         schematic′ κ →
         cpsSubst (λ k → cpsI τ₁ τ₂ τ₃ e (κ (CPSVar k))) v (cpsI τ₁ τ₂ τ₃ e (κ v))
κSubst {τ₁ = τ₁} {τ₂} {.τ₂} {τ} (Val v) κ sch-κ = sch-κ (cpsV τ₁ v)
κSubst {τ₁ = τ₁} {τ₂} {τ₃}  {τ}
        (NonVal (App {τ₁ = .τ₁} {τ₂ = τ₄} {τ₃ = .τ₂} {τ₄ = τ₅} {τ₅ = τ₆} {τ₆ = .τ₃} e₁ e₂)) κ sch-κ =
  κSubst e₁ (λ v' → λ m →
    cpsI τ₄ τ₅ τ₆ e₂
         (λ n → CPSApp (CPSApp (CPSVal m) (CPSVal n))
                (CPSVal (CPSFun (λ a → κ v' (CPSVar a)))))) (λ v₁ →
  κSubst e₂ (λ v' → λ n →
    CPSApp (CPSApp (CPSVal v₁) (CPSVal n))
           (CPSVal (CPSFun (λ a → κ v' (CPSVar a))))) (λ v₂ → sApp Subst≠ (sVal (sFun (λ k' → sch-κ (CPSVar k'))))))
κSubst {τ₁ = τ₁} {τ₂} {.τ₂} {τ} (NonVal (Reset τ₃ .τ₁ .τ₂ e)) κ sch-κ = sLet (λ k' → sch-κ (CPSVar k')) (λ m → Subst≠)
κSubst {τ₁ = τ₁} {τ₂} {τ₃} {τ}  (NonVal (Let {τ₁ = τ₄} {τ₂ = .τ₁} {α = .τ₂} {β = β} {γ = .τ₃} e₁ e₂)) κ sch-κ =
  κSubst e₁ (λ v' → λ n →
    CPSLet (CPSVal n) (λ c → cpsI τ₁ τ₂ β (e₂ c) (κ v'))) λ v₁ →
  sLet (λ c → κSubst (e₂ c) (λ v' → κ v') λ v₂ → sch-κ v₂)
       (λ c → Subst≠)

-- k[v/k] = v ⟶ [e]′@(k[v/k]) = [e′]′@(k[v/k]) = [e′]′@v
kSubst′ : {var : cpstyp → Set} {τ₁ τ₂ τ₃ : typ} →
          (e : term[ var ∘ cpsT ] τ₁ cps[ τ₂ , τ₃ ]) →
          {v : cpsvalue[ var ] (cpsT τ₁ ⇒ cpsT τ₂)} →
          cpsSubst (λ k → cpsI′ τ₁ τ₂ τ₃ e (CPSVar k)) v (cpsI′ τ₁ τ₂ τ₃ e v)
          
kSubst′ (Val v) = sApp (sVal sVar=) (sVal SubstV≠)
kSubst′ {τ₁ = τ₁} {τ₂} {τ₃} (NonVal (App {τ₁ = .τ₁} {τ₂ = τ₄} {τ₃ = .τ₂} {τ₄ = τ₅} {τ₅ = τ₆} {τ₆ = .τ₃} e₁ e₂)) =
  κSubst e₁ (λ v' → λ m →
                     cpsI τ₄ τ₅ τ₆ e₂
                     (λ n → CPSApp (CPSApp (CPSVal m) (CPSVal n)) (CPSVal v'))) λ v₁ → 
  κSubst e₂ (λ v' → (λ n → CPSApp (CPSApp (CPSVal v₁) (CPSVal n)) (CPSVal v'))) λ v₂ → sApp Subst≠ (sVal sVar=)
kSubst′(NonVal (Reset τ₁ τ₂ τ₃ e)) = sLet (λ k' → sApp (sVal sVar=) Subst≠) (λ m → Subst≠)
kSubst′ {τ₁ = τ₁} {τ₂} {τ₃} (NonVal (Let {τ₁ = τ₄} {τ₂ = .τ₁} {α = .τ₂} {β = β} {γ = .τ₃} e₁ e₂)) =
  κSubst e₁ (λ v' → λ n →
    CPSLet (CPSVal n) (λ c → cpsI′ τ₁ τ₂ β (e₂ c) v')) λ v₁ →
  sLet (λ c → kSubst′ (e₂ c)) (λ c → Subst≠)
