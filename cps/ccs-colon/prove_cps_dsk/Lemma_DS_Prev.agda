module Lemma_DS_Prev where

open import CPSterm
open import DStermK
open import DSTrans
open import Lemma_DS_Subst

open import Function
open import Relation.Binary.PropositionalEquality

correctRoot𝑘 : {var : typ𝑘 → Set} → {τ₁ τ₂ τ₃ : cpstyp} →
               {r  : (var ∘ dsT) (τ₁ ⇒[ τ₂ ⇒ τ₂ ]⇒ τ₂) →
                    cpsterm𝑐[ var ∘ dsT ] (τ₂ ⇒ τ₂) τ₃} →
               {r′ : (var ∘ dsT) (τ₁ ⇒[ τ₂ ⇒ τ₂ ]⇒ τ₂) →
                    cpsterm𝑐[ var ∘ dsT ] (τ₂ ⇒ τ₂) τ₃} →
               cpsReduceR r r′ → 
               ReduceRoot𝑘 {var} (dsMain𝑐 τ₁ τ₂ τ₃ r)
                                 (dsMain𝑐 τ₁ τ₂ τ₃ r′)
correctRoot𝑘 {var} {τ₁} {τ₂} {τ₃}
             {.(λ k → CPSApp {_} {τ′} {τ} {τ₂} {τ₃} {τ₂} (CPSFun {_} {τ′} {τ} {τ₂} {τ₃} e₁) v c)}
             {.(λ k → e₂)}
             (βVal𝑐 {τ = τ} {τ′ = τ′} {τ₁ = .τ₁} {τ₂ = .τ₂} {τ₃ = .τ₃}
                    {e₁ = e₁} {v = v} {c = c} {e₂ = e₂} sub) =
  βVal (eSubstVK𝑘 sub)

correctTerm𝑘 : {var : typ𝑘 → Set} → {τ₃ τ₅ : cpstyp} → 
               {e  : cpsterm𝑐[ var ∘ dsT ] (τ₅ ⇒ τ₅) τ₃} →
               {e′ : cpsterm𝑐[ var ∘ dsT ] (τ₅ ⇒ τ₅) τ₃} →
               cpsReduce e e′ → 
               ReduceTerm𝑘 {var} (dsE𝑐 τ₃ τ₅ e)
                                 (dsE𝑐 τ₃ τ₅ e′)
correctTerm𝑘 {var} {τ₃} {τ₅}
             {.(CPSRet {_} {τ₁} {τ₃} {τ₅} (CPSCont {_} {τ₁} {τ₃} {τ₃} {τ₅} e) v)}
             {e′}
             (βLet𝑐 {τ₁ = τ₁} {τ₂ = .τ₃} {τ₄ = .τ₅} {v = v} {e = e} {e′ = .e′} sub) =
  βLet (eSubstV𝑘 sub)
  
correctTermId𝑘 : {var : typ𝑘 → Set} → {τ₃ τ₅ : cpstyp} → 
                 {e  : cpsterm𝑐[ var ∘ dsT ] (τ₅ ⇒ τ₅) τ₃} →
                 {e′ : cpsterm𝑐[ var ∘ dsT ] (τ₅ ⇒ τ₅) τ₃} →
                 cpsReduce• e e′ → 
                 ReduceTerm𝑘𝑠 {var}
                   (NonVal Hole (Reset (dsT τ₅) (dsT τ₃) (dsT τ₃)
                     (dsE𝑐 τ₃ τ₅ e)))
                   (NonVal Hole (Reset (dsT τ₅) (dsT τ₃) (dsT τ₃)
                     (dsE𝑐 τ₃ τ₅ e′)))
correctTermId𝑘 {var} {τ₃} {τ₅}
               {.(CPSApp {_} {τ₁} {(τ₁ ⇒[ τ₃ ⇒ τ₄ ]⇒ τ₄) ⇒[ τ₅ ⇒ τ₅ ]⇒ τ₃} {τ₃} {τ₃} {τ₅}
                 (CPSShift {_} {τ₁} {τ₃} {τ₄} {τ₅} {τ₃}) w j)}
               {.(CPSApp {_} {τ₅} {τ₁ ⇒[ τ₃ ⇒ τ₄ ]⇒ τ₄} {τ₅} {τ₃} {τ₅}
                         w
                         (CPSFun {_} {τ₃} {τ₁} {τ₄} {τ₄}
                         (λ x k → CPSRetE {_} {τ₅} {τ₃} {τ₄} {τ₄}
                                  (CPSKVar {_} {τ₃} {τ₄} {τ₄} k)
                                  (CPSRet {_} {τ₁} {τ₃} {τ₅}
                                          j (CPSVar {_} {τ₁} x))))
                         (CPSId {_} {τ₅} {τ₃}))}
               (βShift𝑐 {τ₁ = τ₁} {τ₂ = .τ₃} {τ₃ = τ₄} {τ₄ = .τ₅} {w = w} {j = j}) =
  βShift {τ₂ = dsT τ₃}


correctVal𝑘 : {var : typ𝑘 → Set} → {τ₁ : cpstyp} →
              {v  : cpsvalue𝑐[ var ∘ dsT ] τ₁} →
              {v′ : cpsvalue𝑐[ var ∘ dsT ] τ₁} →
              cpsReduceV v v′ →
              ReduceVal𝑘 {var} (dsV𝑐 τ₁ v) (dsV𝑐 τ₁ v′)
correctVal𝑘 {var} {.(τ₂ ⇒[ τ₁ ⇒ τ₃ ]⇒ τ₄)}
            {.(CPSFun {_} {τ₁} {τ₂} {τ₃} {τ₄}
              (λ x k → CPSApp {_} {τ₁} {τ₂} {τ₃} {τ₄} {τ₃}
                               v′ (CPSVar {_} {τ₂} x)
                               (CPSKVar {_} {τ₁} {τ₃} {τ₄} k)))}
            {v′}
            (ηVal𝑐 {τ₁ = τ₁} {τ₂ = τ₂} {τ₃ = τ₃} {τ₄ = τ₄} {v = .v′}) =
  ηVal

correctCon𝑘 : {var : typ𝑘 → Set} → {τ₁ τ₂ τ₃ τ₅ : cpstyp} →
              {k  : cpscont𝑐[ var ∘ dsT ] (τ₅ ⇒ τ₅) τ₃ (τ₁ ⇒ τ₂)} →
              {k′ : cpscont𝑐[ var ∘ dsT ] (τ₅ ⇒ τ₅) τ₃ (τ₁ ⇒ τ₂)} →
              cpsReduceK k k′ →
              ReduceCon𝑘 {var} (dsC𝑐 τ₁ τ₂ τ₃ τ₅ k)
                               (dsC𝑐 τ₁ τ₂ τ₃ τ₅ k′)
correctCon𝑘 {var} {τ₁} {τ₂} {.τ₂} {τ₅}
            {.(CPSCont {_} {τ₁} {τ₂} {τ₂} {τ₅}
              (λ x → CPSRet {_} {τ₁} {τ₂} {τ₅} k′ (CPSVar {_} {τ₁} x)))}
            {k′}
            (ηLet𝑐 {τ₁ = .τ₁} {τ₂ = .τ₂} {τ₃ = .τ₅} {k = .k′}) = ηLet
