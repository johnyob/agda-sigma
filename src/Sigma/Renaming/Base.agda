-- ----------------------------------------------------------------------
-- The Agda σ-library
-- 
-- Renamings
-- ----------------------------------------------------------------------

-- A renaming is defined as a substitution ρ, mapping 
-- indices to indices (w/ explicit bounds). It is a subclass
-- of substitutions.
-- 
-- The σ-library provides renamings as primitives.

module Sigma.Renaming.Base where

open import Data.Nat using (ℕ; suc; zero; _+_)
open import Data.Fin using (Fin; zero; suc)

open import Function as Fun using (_∘_)

open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)

open import Sigma.Subst.Base using (Sub; _∷_; []; _++_)

-- ------------------------------------------------------------------------

-- A renaming ρ : 𝕀ⁿ → 𝕀ᵐ is denoted { i ↦ j : i ∈ 𝕀ⁿ, j ∈ 𝕀ᵐ }
Ren : ℕ → ℕ → Set 
Ren m n = Sub (Fin n) m

space : ∀ { m n } → Ren m n → ℕ × ℕ
space { m } { n } _ = ⟨ m , n ⟩

dom : ∀ { m n } → Ren m n → ℕ
dom = proj₁ ∘ space

rng : ∀ { m n } → Ren m n → ℕ
rng = proj₂ ∘ space

-- Identity renaming idₙ : 𝕀ⁿ → 𝕀ⁿ. 
-- Defined by idₙ = { i ↦ i : i ∈ 𝕀ⁿ }.
id : ∀ { n } → Ren n n
id = Fun.id

-- Shift operator ↑ₙ : 𝕀ⁿ → 𝕀ⁿ⁺¹
-- Defined by ↑ₙ i = 1 + i
↑ : ∀ { n } → Ren n (1 + n)
↑ = suc

infix 10 _⇑ 

-- Lift operator ρ ⇑
-- Defined by ρ ⇑ = { 0 ↦ 0 } ∪ { ↑ i ↦ ↑ j : i ∈ 𝕀ⁿ, j ∈ 𝕀ᵐ }
-- This operator is used for defining a capture avoiding renaming. 
-- 
-- For example in λ. e, free variables of e are now shifted:
--  e   :     0   1   2
--  λ e : 0   1   2   3
-- since λ binds 0. 
_⇑ : ∀ { m n } → Ren m n → Ren (1 + m) (1 + n)
ρ ⇑ = zero ∷ ↑ ∘ ρ

-- ------------------------------------------------------------------------

-- Generalizing the above primitives to "multi-variable binders"
-- allows for formalization of binders that bind multiple variables,
-- such as patterns. So-called multi-variate binders. 

-- Multi-variate identity idₙᵐ : 𝕀ᵐ → 𝕀ᵐ⁺ⁿ 
-- Defined by idₙᵐ = { i ↦ i' : i ∈ 𝕀ᵐ, i' ∈ 𝕀ᵐ⁺ⁿ, i = i' }.
-- 
-- For example:
-- id✶ 1 = 0 ∷ []ₙ 
-- id✶ 2 = 0 ∷ ↑ ∘ (0 ∷ []) = 0 ∷ 1 ∷ []ₙ 
-- id✶ 3 = 0 ∷ ↑ ∘ id✶ 2 = 0 ∷ 1 ∷ 2 ∷ []ₙ 
id✶ : ∀ { n } m → Ren m (m + n)
id✶ zero = []
id✶ (suc m) = zero ∷ ↑ ∘ id✶ m

-- Multi-variate shift operator ↑ₙᵐ : 𝕀ⁿ → 𝕀ᵐ⁺ⁿ
-- Defined by ↑ₙᵐ = { i ↦ m + i : i ∈ 𝕀ⁿ }
↑✶_ : ∀ { n } k → Ren n (k + n)
↑✶ zero = id
↑✶ suc k = ↑ ∘ ↑✶ k

-- Multi-variate lift operator ρ ⇑ᵏ 
-- Defined by ρ ⇑ᵏ = { i ↦ i' } ∪ { ↑ᵏ i ↦ ↑ᵏ j : i ∈ 𝕀ⁿ, j ∈ 𝕀ᵐ }
-- This operator is used for defining a multi-variate capture avoiding renaming. 
-- 
-- For example in λ. e, free variables of e are now shifted by k:
--  e   :         0   1       2       3
--  λ e : 0   ... k   k + 1   k + 2   k + 3
-- since λ binds 0, ..., k - 1. 
_⇑✶_ :  ∀ { m n } → Ren m n → ∀ k → Ren (k + m) (k + n)
ρ ⇑✶ k = id✶ k ++ (↑✶ k ∘ ρ)
