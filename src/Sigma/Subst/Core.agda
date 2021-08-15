-- ----------------------------------------------------------------------
-- The Agda σ-library
-- 
-- Substitutions
-- ----------------------------------------------------------------------

module Sigma.Subst.Core where

open import Sigma.Renaming.Base

open import Data.Nat using (ℕ; _+_)
open import Data.Fin using (Fin)

open import Function using (_∘_)

open import Data.Product using (_×_; proj₁; proj₂) renaming ( _,_ to ⟨_,_⟩ )

-- ----------------------------------------------------------------------

open import Sigma.Subst.Base public

splitAt : ∀ m { n } { T } 
  → Sub T (m + n)
  -- -------------
  → Sub T m × Sub T n
splitAt m σ = ⟨ σ ∘ (id✶ m) , σ ∘ (↑✶ m) ⟩

take : ∀ m { n } { T }
  → Sub T (m + n)
  → Sub T m
take m σ = proj₁ (splitAt m σ)

drop : ∀ m { n } { T }
  → Sub T (m + n)
  → Sub T n
drop m σ = proj₂ (splitAt m σ)
