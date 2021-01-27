module lemma1 where

open import DSterm
open import CPSterm
open import reasoning

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
  eκSubst (sReset sub) eq =
    sApp (sVal (sFun (λ m → eq sVar≠))) (eκSubst sub (λ m → sVal m))
  eκSubst (sLet sub₂ sub₁) eq =
    eκSubst sub₁ (λ m → sApp (sVal (sFun (λ c → eκSubst (sub₂ c) eq))) (sVal m))
     
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
  ekSubst′ k (sReset sub) =
    sApp Subst≠ (eκSubst sub (λ m → sVal m))

  ekSubst′ k (sLet sub₂ sub₁) =
    eκSubst sub₁
            (λ m → sApp (sVal (sFun (λ c → ekSubst′ k (sub₂ c))))
                         (sVal m))

{----------------SCHEMATIC----------------}
     
schematic : {var : cpstyp → Set} {τ₁ τ₂ : typ} →
             (κ : cpsvalue[ var ] (cpsT τ₁) →
                   cpsterm[ var ] (cpsT τ₂)) → Set
schematic {var} {τ₁} {τ₂} κ =
  {α : typ} → 
  (v₁ : var (cpsT α) → cpsvalue[ var ] (cpsT τ₁)) →
  (v₁′ : cpsvalue[ var ] (cpsT τ₁)) →
  (v : cpsvalue[ var ] (cpsT α)) →
  cpsSubstVal v₁ v v₁′ → 
  cpsSubst (λ y → κ (v₁ y)) v (κ v₁′)

schematic′ : {var : cpstyp → Set} {τ₁ τ₂ : typ} {τ : cpstyp} →
             (κ : cpsvalue[ var ] τ →
                   cpsvalue[ var ] (cpsT τ₁) → cpsterm[ var ] (cpsT τ₂)) → Set
schematic′ {var} {τ₁} {τ₂} {τ} κ =
  {α : cpstyp} → 
  {v₁ : var α → cpsvalue[ var ] τ} →
  {v₁′ : cpsvalue[ var ] τ} → 
  {v : cpsvalue[ var ] α} →
  (x : cpsvalue[ var ] (cpsT τ₁)) →
  cpsSubstVal v₁ v v₁′ → 
  cpsSubst (λ y → κ (v₁ y) x) v (κ v₁′ x)

κSubst : {var : cpstyp → Set} {τ₁ τ₂ τ₃ : typ} →
          (e : term[ var ∘ cpsT ] τ₁ cps[ τ₂ , τ₃ ]) →
          {τ τ′ : cpstyp} → 
          {v : cpsvalue[ var ] τ′} → 
          (κ : cpsvalue[ var ] τ →
                cpsvalue[ var ] (cpsT τ₁) → cpsterm[ var ] (cpsT τ₂)) →
          {v₁ : var τ′ → cpsvalue[ var ] τ} →
          {v₁′ : cpsvalue[ var ] τ} → 
          schematic′ κ → 
          cpsSubstVal v₁ v v₁′ →
          cpsSubst (λ k → cpsI τ₁ τ₂ τ₃ e (κ (v₁ k))) v (cpsI τ₁ τ₂ τ₃ e (κ v₁′))
           
κSubst {var} {τ₁} {τ₂} {.τ₂} (Val {τ₁ = .τ₁} {τ₂ = .τ₂} x) {τ} {v} κ {v₁} {v₁′} sche sub𝑣 = sche (cpsV τ₁ x) sub𝑣

κSubst {var} {τ₁} {τ₂} {τ₃} (NonVal {τ₁ = .τ₁} {τ₂ = .τ₂} {τ₃ = .τ₃}
        (App {τ₁ = .τ₁} {τ₂ = τ₄} {τ₃ = .τ₂} {τ₄ = τ₅} {τ₅ = τ₆} {τ₆ = .τ₃} e₁ e₂)) {τ} {v} κ {v₁} {v₁′} sche sub𝑣 =
  κSubst e₁
          (λ v′ m → cpsI τ₄ τ₅ τ₆ e₂
          (λ n → CPSApp (CPSApp (CPSVal m) (CPSVal n))
                         (CPSVal (CPSFun (λ a → κ v′ (CPSVar a))))))
          (λ {α} x₁ sub₁ →
  κSubst e₂
          (λ v′ n → CPSApp (CPSApp (CPSVal x₁) (CPSVal n))
                            (CPSVal (CPSFun (λ a → κ v′ (CPSVar a)))))
          (λ x₂ sub₂ → sApp Subst≠ (sVal (sFun (λ a → sche (CPSVar a) sub₂))))
          sub₁)
          sub𝑣
        
κSubst {var} {τ₁} {τ₂} {.τ₂}
         (NonVal {τ₁ = .τ₁} {τ₂ = .τ₂} {τ₃ = .τ₂} (Reset τ₃ .τ₁ .τ₂ e)) {τ} {v} κ {v₁} {v₁′} sche sub𝑣 =
  sApp (sVal (sFun (λ m → sche (CPSVar m) sub𝑣))) Subst≠
   
κSubst {var} {τ₁} {τ₂} {τ₃}
         (NonVal {τ₁ = .τ₁} {τ₂ = .τ₂} {τ₃ = .τ₃}
                 (Let {τ₁ = τ₄} {τ₂ = .τ₁} {α = .τ₂} {β = β} {γ = .τ₃} e₁ e₂)) {τ} {v} κ {v₁} {v₁′} sche sub𝑣 =
  κSubst e₁
          (λ v′ m → CPSApp (CPSVal (CPSFun (λ c → cpsI τ₁ τ₂ β (e₂ c) (κ v′)))) (CPSVal m))
          (λ x₁ sub₁ → sApp (sVal (sFun (λ c →
  κSubst (e₂ c) κ (λ x₂ sub₂ → sche x₂ sub₂) sub₁))) Subst≠)
  sub𝑣
  
kSubst′ : {var : cpstyp → Set} {τ₁ τ₂ τ₃ : typ} →
          {τ′ : cpstyp} → 
          (e : term[ var ∘ cpsT ] τ₁ cps[ τ₂ , τ₃ ]) →
          {v₁ : var τ′ → cpsvalue[ var ] (cpsT τ₁ ⇒ cpsT τ₂)} → 
          {v₁′ : cpsvalue[ var ] (cpsT τ₁ ⇒ cpsT τ₂)}
          {v : cpsvalue[ var ] τ′} →
          cpsSubstVal v₁ v v₁′ → 
          cpsSubst (λ k → cpsI′ τ₁ τ₂ τ₃ e (v₁ k)) v (cpsI′ τ₁ τ₂ τ₃ e v₁′)

kSubst′ (Val x) subv = sApp (sVal subv) Subst≠
kSubst′ {var} {τ₁} {τ₂} {τ₃}
        (NonVal {τ₁ = .τ₁} {τ₂ = .τ₂} {τ₃ = .τ₃}
        (App {τ₁ = .τ₁} {τ₂ = τ₄} {τ₃ = .τ₂} {τ₄ = τ₅} {τ₅ = τ₆} {τ₆ = .τ₃} e₁ e₂)) {v₁} {v₁′} {v} subv =
  κSubst e₁
          (λ v′ m → cpsI τ₄ τ₅ τ₆ e₂
          (λ n → CPSApp (CPSApp (CPSVal m) (CPSVal n)) (CPSVal v′))) {v₁} {v₁′}
          (λ x₁ sub₁ →
  κSubst e₂
          (λ v′ n → CPSApp (CPSApp (CPSVal x₁) (CPSVal n)) (CPSVal v′))
          (λ x₂ sub₂ → sApp Subst≠ (sVal sub₂)) sub₁)
          subv

kSubst′ {var} {τ₁} {τ₂} {.τ₂}
        (NonVal {τ₁ = .τ₁} {τ₂ = .τ₂} {τ₃ = .τ₂} (Reset τ₃ .τ₁ .τ₂ x)) {v₁} {v₁′} {v} subv =
  sApp (sVal subv) Subst≠
  
kSubst′ {var} {τ₁} {τ₂} {τ₃}
        (NonVal {τ₁ = .τ₁} {τ₂ = .τ₂} {τ₃ = .τ₃}
        (Let {τ₁ = τ₄} {τ₂ = .τ₁} {α = .τ₂} {β = β} {γ = .τ₃} e₁ e₂)) {v₁} {v₁′} {v} subv =
  κSubst e₁
         (λ v′ m → CPSApp (CPSVal (CPSFun (λ c → cpsI′ τ₁ τ₂ β (e₂ c) v′))) (CPSVal m))
         (λ x₁ sub₁ → sApp (sVal (sFun (λ c → kSubst′ (e₂ c) sub₁))) Subst≠) subv

eSubst : {var : cpstyp → Set} {τ₁ τ₂ τ₃ τ : typ} →
         {e₁ : var (cpsT τ) →
               term[ var ∘ cpsT ] τ₁ cps[ τ₂ , τ₃ ]} →
         {e₂ : term[ var ∘ cpsT ] τ₁ cps[ τ₂ , τ₃ ]} →
         {v : value[ var ∘ cpsT ] τ cps[τ,τ]} →
         {κ : cpsvalue[ var ] (cpsT τ₁) → cpsterm[ var ] (cpsT τ₂)} →
         Subst e₁ v e₂ →
         schematic κ →
         cpsSubst (λ x → cpsI τ₁ τ₂ τ₃ (e₁ x) κ)
                  (cpsV τ v)
                  (cpsI τ₁ τ₂ τ₃ e₂ κ)
                  
eSubst {var} {τ₁} {τ₂} {.τ₂} {τ}
       {.(λ y → Val {_} {τ₁} {τ₂} (v₁ y))} {.(Val {_} {τ₁} {τ₂} v₁′)} {v} {κ}
       (sVal {τ = .τ} {τ₁ = .τ₁} {τ₂ = .τ₂} {v₁ = v₁} {v = .v} {v₁′ = v₁′} subv) sche =
       sche (λ x → cpsV τ₁ (v₁ x)) (cpsV τ₁ v₁′) (cpsV τ v) (eSubstV subv)

eSubst {var} {τ₁} {τ₂} {τ₃} {τ}
       {.(λ y → NonVal {_} {τ₁} {τ₂} {τ₃} (App {_} {τ₁} {τ₄} {τ₂} {τ₅} {τ₆} {τ₃} (e₁ y) (e₂ y)))}
       {.(NonVal {_} {τ₁} {τ₂} {τ₃} (App {_} {τ₁} {τ₄} {τ₂} {τ₅} {τ₆} {τ₃} e₁′ e₂′))} {v} {κ}
       (sApp {τ = .τ} {τ₁ = .τ₁} {τ₂ = τ₄} {τ₃ = .τ₂} {τ₄ = τ₅} {τ₅ = τ₆} {τ₆ = .τ₃} {e₁ = e₁}
             {e₂ = e₂} {v = .v} {e₁′ = e₁′} {e₂′ = e₂′} sub₁ sub₂) sche =
       eκSubst sub₁ (λ m → eκSubst sub₂
                    (λ n → sApp (sApp (sVal m) (sVal n))
                                (sVal (sFun (λ a → sche (λ x → CPSVar a) (CPSVar a) (cpsV τ v) SubstV≠)))))
eSubst {τ₁ = τ₁} {τ₂} {.τ₂} {τ}
       {.(λ y → NonVal {_} {τ₁} {τ₂} {τ₂} (Reset τ₃ τ₁ τ₂ (e₁ y)))}
       {.(NonVal {_} {τ₁} {τ₂} {τ₂} (Reset τ₃ τ₁ τ₂ e₁′))} {v} {κ}
       (sReset {τ = .τ} {τ₁ = τ₃} {τ₂ = .τ₁} {τ₃ = .τ₂} {e₁ = e₁} {v = .v} {e₁′ = e₁′} sub) sche =
  sApp Subst≠ (eSubst sub (λ v₁ v₁′ v₂ x → sVal x))
       
eSubst (sLet sub₂ sub₁) sche =
  eκSubst sub₁ (λ m → sApp (sVal (sFun (λ c → eSubst (sub₂ c) sche))) (sVal m))
