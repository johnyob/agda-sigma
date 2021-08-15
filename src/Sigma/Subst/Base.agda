-- ----------------------------------------------------------------------
-- The Agda σ-library
-- 
-- Substitutions
-- ----------------------------------------------------------------------

-- A substitution on T is defined as a mapping from
-- indices to T (w/ explicit bounds).
-- 
-- Since the domain is bounded, we may think
-- of substitutions as vectors. 

module Sigma.Subst.Base where

open import Data.Nat using (ℕ; suc; zero; _+_)
open import Data.Fin using (Fin; zero; suc)

open import Function using (_∘_)

open import Data.Product using (_×_) renaming ( _,_ to ⟨_,_⟩ )

-- ----------------------------------------------------------------------

-- A subsitution σ : 𝕀ⁿ → T is denoted { i ↦ x : i ∈ 𝕀ⁿ, x ∈ T }
Sub : Set → ℕ → Set 
Sub T m = Fin m → T


-- The empty subsitution. 
-- Note that 𝕀⁰ ≡ ⊥. We note σ : 𝕀⁰ → T by []
-- Intuitively, this mimics an empty vector. 
[] : ∀ { T } → Sub T 0
[] = λ ()

infixr 5 _∷_ 

-- The σ-cons operator ∷ ∶ T → (𝕀ⁿ → T) → (𝕀¹⁺ⁿ → T)
-- 
-- Intuitively, the σ-cons operator mimics the 
-- semantics of cons operator on vectors. 
-- 
-- x ∷ ρ = { 0 ↦ x } ∪ { 1 + i ↦ ρ i : i ∈ 𝕀ⁿ }
_∷_ : ∀ { n } { T } → T → Sub T n → Sub T (1 + n)
(x ∷ σ) zero = x
(x ∷ σ) (suc n) = σ n

[_] : ∀ { T } → T → Sub T 1
[ x ] = x ∷ []

head : ∀ { n } { T } → Sub T (1 + n) → T
head σ = σ zero

tail : ∀ { n } { T } → Sub T (1 + n) → Sub T n
tail σ = σ ∘ suc

map : ∀ { n } { T U } → (T → U) → Sub T n → Sub U n
map f σ = f ∘ σ

uncons : ∀ { n } { T } → Sub T (1 + n) → T × Sub T n 
uncons σ = ⟨ head σ , tail σ ⟩


infixr 5 _++_

-- The σ-append operator ++ : (𝕀ᵐ → T) → (𝕀ⁿ → T) → (𝕀ᵐ⁺ⁿ → T)
-- 
-- σ₁ ++ σ₂ = { i ↦ σ₁ i : i ∈ 𝕀ᵐ⁺ⁿ, i < m } ∪ { i ↦ σ₂ i : i ∈ 𝕀ᵐ⁺ⁿ, i ≥ m }
_++_ : ∀ { m n } { T } → Sub T m → Sub T n → Sub T (m + n)
_++_ {zero} σ₁ σ₂ = σ₂
_++_ {suc m} σ₁ σ₂ = σ₁ zero ∷ (σ₁ ∘ suc) ++ σ₂


