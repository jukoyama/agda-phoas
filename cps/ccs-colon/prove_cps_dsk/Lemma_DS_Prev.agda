module Lemma_DS_Prev where

open import CPSterm
open import DStermK
open import DSTrans
open import Lemma_DS_Subst

open import Function
open import Relation.Binary.PropositionalEquality

correctTerm𝑘 : {var : typ𝑘 → Set} → {τ₃ τ₅ : cpstyp} → 
               {e  : cpsterm𝑐[ var ∘ dsT ] (τ₅ ⇒ τ₅) τ₃} →
               {e′ : cpsterm𝑐[ var ∘ dsT ] (τ₅ ⇒ τ₅) τ₃} →
               cpsReduce e e′ → 
               ReduceTerm𝑘 {var} (dsE𝑐 τ₃ τ₅ e)
                                 (dsE𝑐 τ₃ τ₅ e′)
correctTerm𝑘 {var} {τ₃} {τ₅}
             {.(CPSApp {_} {τ₁} {τ₀} {τ₄} {τ₃} {τ₅}
                       (CPSFun {_} {τ₅} {τ₀} {τ₁} {τ₅} {τ₄} {τ₃} e₁) v c)}
             {e′}
             (βVal𝑐 {τ₀ = τ₀} {τ₁ = τ₁} {τ₂ = .τ₅} {τ₃ = τ₄} {τ₄ = .τ₃}
                     {e₁ = e₁} {v = v} {c = c} {e₂ = .e′} sub) =
  βVal (eSubstVK𝑘 sub)
  
correctTerm𝑘 {var} {τ₃} {τ₅}
             {.(CPSRet {_} {τ₁} {τ₃} {τ₅}
                       (CPSCont {_} {τ₁} {τ₃} {τ₃} {τ₅} e) v)}
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
               {.(CPSApp {_} {τ₄} {(τ₄ ⇒[ τ₃ ⇒ τ₄ ]⇒ τ₄) ⇒[ τ₅ ⇒ τ₅ ]⇒ τ₃} {τ₃} {τ₃} {τ₅}
                         (CPSShift {_} {τ₄} {τ₃} {τ₄} {τ₅} {τ₃}) w j)}
               {.(CPSApp {_} {τ₅} {τ₄ ⇒[ τ₃ ⇒ τ₄ ]⇒ τ₄} {τ₅} {τ₃} {τ₅}
                         w
                         (CPSFun {_} {τ₄} {τ₄} {τ₃} {τ₄} {τ₄} {τ₄}
                                 (λ x k → CPSRetE {_} {τ₅} {τ₃} {τ₄} {τ₄}
                                          (CPSKVar {_} {τ₃} {τ₄} {τ₄} k)
                                          (CPSRet {_} {τ₄} {τ₃} {τ₅}
                                                  j
                                                  (CPSVar {_} {τ₄} x))))
                         (CPSId {_} {τ₅} {τ₃}))}
               (βShift𝑐 {τ₁ = .τ₅} {τ₃ = τ₄} {τ₄ = .τ₃} {w = w} {j = j}) =
  βShift

correctTermId𝑘𝑆 : {var : typ𝑘 → Set} → {τ₂ : cpstyp} →
                  {e : cpsterm𝑐[ var ∘ dsT ] (τ₂ ⇒ τ₂) τ₂} →
                  {v : cpsvalue𝑐[ var ∘ dsT ] τ₂} →
                  cpsReduce𝑅 e v →
                  ReduceTerm𝑘𝑅 {var}
                    (NonVal Hole (Reset (dsT τ₂) (dsT τ₂) (dsT τ₂) (dsE𝑐 τ₂ τ₂ e)))
                    (dsV𝑐 τ₂ v)
correctTermId𝑘𝑆 {var} {τ₂}
                {.(CPSRet {_} {τ₂} {τ₂} {τ₂} (CPSId {_} {τ₂} {τ₂}) v)}
                {v}
                (βReset𝑐 {τ₁ = .τ₂} {v = .v}) =
  βReset

correctVal𝑘 : {var : typ𝑘 → Set} → {τ₁ : cpstyp} →
              {v  : cpsvalue𝑐[ var ∘ dsT ] τ₁} →
              {v′ : cpsvalue𝑐[ var ∘ dsT ] τ₁} →
              cpsReduceV v v′ →
              ReduceVal𝑘 {var} (dsV𝑐 τ₁ v) (dsV𝑐 τ₁ v′)
correctVal𝑘 {var} {.(τ₀ ⇒[ τ₁ ⇒ τ₃ ]⇒ τ₄)}
            {.(CPSFun {_} {τ₃} {τ₀} {τ₁} {τ₃} {τ₃} {τ₄}
                      (λ x k → CPSApp {_} {τ₁} {τ₀} {τ₃} {τ₄} {τ₃}
                                       v′ (CPSVar {_} {τ₀} x) (CPSKVar {_} {τ₁} {τ₃} {τ₄} k)))}
            {v′} (ηVal𝑐 {τ₀ = τ₀} {τ₁ = τ₁} {τ₃ = τ₃} {τ₄ = τ₄} {v = .v′}) =
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
