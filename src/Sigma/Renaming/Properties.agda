module Sigma.Renaming.Properties where

open import Data.Nat using (ℕ; _+_; zero; suc)
open import Data.Fin using (Fin; zero; suc)

open import Sigma.Subst.Core
open import Sigma.Renaming.Base

open import Sigma.Subst.Properties using (extensionality)

open import Function using (_∘_)

open import Relation.Binary.PropositionalEquality as Eq
  using (_≡_; refl; cong; cong₂)
open Eq.≡-Reasoning

-- ------------------------------------------------------------------------

⇑-cong : ∀ { m n } { ρ₁ ρ₂ : Ren m n } 
  → ρ₁ ≡ ρ₂
  -- -----------
  → ρ₁ ⇑ ≡ ρ₂ ⇑
⇑-cong ρ₁≡ρ₂ = cong (_⇑) ρ₁≡ρ₂


⇑✶-cong : ∀ { m n } k { ρ₁ ρ₂ : Ren m n } 
  → ρ₁ ≡ ρ₂
  -- -----------
  → ρ₁ ⇑✶ k  ≡ ρ₂ ⇑✶ k
⇑✶-cong k ρ₁≡ρ₂ = cong (_⇑✶ k) ρ₁≡ρ₂

-- ------------------------------------------------------------------------

∘-⇑-distrib : ∀ { m n k } ( ρ₁ : Ren m n ) ( ρ₂ : Ren n k )
  → (ρ₂ ⇑ ∘ ρ₁ ⇑) ≡ (ρ₂ ∘ ρ₁) ⇑
∘-⇑-distrib ρ₁ ρ₂ = extensionality lemma
  where 
    lemma : ∀ x → (ρ₂ ⇑ ∘ ρ₁ ⇑) x ≡ ((ρ₂ ∘ ρ₁) ⇑) x
    lemma zero = refl
    lemma (suc x) = refl

-- TODO:
-- generalized for ⇑✶

-- ------------------------------------------------------------------------

⇑-id : ∀ { n } → (id { n }) ⇑ ≡ id
⇑-id = extensionality lemma
  where 
    lemma : ∀ { n } x → (id { n } ⇑) x ≡ x
    lemma zero = refl
    lemma (suc x) = refl