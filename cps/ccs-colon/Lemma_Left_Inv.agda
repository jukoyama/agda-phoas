module Lemma_Left_Inv where

open import DStermK
open import CPSterm
open import CPSIsm
open import DSTrans

open import Function
open import Relation.Binary.PropositionalEquality
open import Data.Product

Left_Inv : {var : typ𝑘 → Set} → {τ₁ τ₂ τ₃ : typ𝑘} →
           {e : root𝑘[ (var ∘ dsT) ∘ cpsT𝑘 ] dsT (cpsT𝑘 τ₁)
                    cps[ dsT (cpsT𝑘 τ₂) , dsT (cpsT𝑘 τ₃) ]} →
           e
           ≡
           dsMain𝑐 {!!} {!!} {!!} (cpsMain𝑘 {!!} {!!} {!!} {!e!})
Left_Inv = {!!}
           
