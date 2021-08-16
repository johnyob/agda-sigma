module SystemF where

open import Data.Nat using (ℕ; zero; suc; _+_)

open import Data.Fin as Fin using (Fin; zero; suc)

open import Function as Fun using (_∘_)

open import Relation.Binary.PropositionalEquality as Eq
  using (_≡_; refl; cong; cong₂; cong-app; sym)
open Eq.≡-Reasoning

-- ------------------------------------------------------------------------

infixr 7 _⇒_
infix 9 `_

data Type (n : ℕ) : Set where
  `_ : Fin n → Type n
  _⇒_ : Type n → Type n → Type n
  `∀ : Type (1 + n) → Type n


⇒-cong : ∀ { n } { τ₁¹ τ₁² τ₂¹ τ₂² : Type n } 
  → τ₁¹ ≡ τ₂¹
  → τ₁² ≡ τ₂²
  -- ----------------------
  → τ₁¹ ⇒ τ₁² ≡ τ₂¹ ⇒ τ₂²
⇒-cong ≡τ¹ ≡τ² = cong₂ _⇒_ ≡τ¹ ≡τ²

`∀-cong : ∀ { n } { τ₁ τ₂ : Type (1 + n) } 
  → τ₁ ≡ τ₂
  -- -------------
  → `∀ τ₁ ≡ `∀ τ₂
`∀-cong ≡τ = cong `∀ ≡τ

-- ------------------------------------------------------------------------

open import Sigma.Subst.Core
open import Sigma.Renaming.Base

ren-τ : ∀ { m n } → Ren m n → Type m → Type n
ren-τ ρ (` α) = ` ρ α
ren-τ ρ (τ₁ ⇒ τ₂) = ren-τ ρ τ₁  ⇒ ren-τ ρ τ₂
ren-τ ρ (`∀ τ) = `∀ (ren-τ (ρ ⇑) τ)


_⇑τ : ∀ { m n } → Sub (Type n) m → Sub (Type (1 + n)) (1 + m)
σ ⇑τ = ` zero ∷ (ren-τ ↑ ∘ σ)

sub-τ : ∀ { m n } → Sub (Type n) m → Type m → Type n
sub-τ σ (` α) = σ α
sub-τ σ (τ₁ ⇒ τ₂) = sub-τ σ τ₁ ⇒ sub-τ σ τ₂
sub-τ σ (`∀ τ) = `∀ (sub-τ (σ ⇑τ) τ)

-- ------------------------------------------------------------------------

open import Sigma.Subst.Properties using (extensionality)
open import Sigma.Renaming.Properties using (∘-⇑-distrib; ⇑-id)

-- ------------------------------------------------------------------------
-- Congruences
-- ------------------------------------------------------------------------

ren-τ-cong : ∀  { m n } { ρ₁ ρ₂ : Ren m n }
  → ρ₁ ≡ ρ₂
  -- -------
  → ren-τ ρ₁ ≡ ren-τ ρ₂ 
ren-τ-cong ρ₁≡ρ₂ = cong ren-τ ρ₁≡ρ₂

⇑τ-cong : ∀ { m n } { σ₁ σ₂ : Sub (Type n) m } 
  → σ₁ ≡ σ₂
  -- ------------
  → σ₁ ⇑τ ≡ σ₂ ⇑τ
⇑τ-cong σ₁≡σ₂ = cong _⇑τ  σ₁≡σ₂

-- ⇑τ✶-cong 

sub-τ-cong : ∀ { m n } { σ₁ σ₂ : Sub (Type n) m }
  → σ₁ ≡ σ₂
  -- --------
  → sub-τ σ₁ ≡ sub-τ σ₂
sub-τ-cong σ₁≡σ₂ = cong sub-τ σ₁≡σ₂


-- ------------------------------------------------------------------------
-- Coincidence Laws
-- ------------------------------------------------------------------------
-- Every renaming can form a subsitution 

⇑τ-coincidence : ∀ { m n } (ρ : Ren m n)
  → `_ ∘ (ρ ⇑) ≡ (`_ ∘ ρ) ⇑τ
⇑τ-coincidence ρ = extensionality lemma
  where 
    lemma : ∀ x → ` ((ρ ⇑) x) ≡ ((`_ ∘ ρ) ⇑τ) x
    lemma zero = refl
    lemma (suc x) = refl

ren-τ-coincidence : ∀ { m n } (ρ : Ren m n)
  → ren-τ ρ ≡ sub-τ (`_ ∘ ρ)
ren-τ-coincidence ρ = extensionality (lemma ρ)
  where 
    lemma : ∀ { m n } (ρ : Ren m n)
      → ∀ τ → ren-τ ρ τ ≡ sub-τ (`_ ∘ ρ) τ
    lemma ρ (` α) = refl
    lemma ρ (τ₁ ⇒ τ₂) = ⇒-cong (lemma ρ τ₁) (lemma ρ τ₂)
    lemma ρ (`∀ τ) = `∀-cong (
      begin 
        ren-τ (ρ ⇑) τ 
      ≡⟨ lemma (ρ ⇑) τ ⟩ 
        sub-τ (`_ ∘ (ρ ⇑)) τ 
      ≡⟨ cong-app (sub-τ-cong (⇑τ-coincidence ρ)) τ ⟩ 
        sub-τ ((`_ ∘ ρ) ⇑τ) τ 
      ∎)

-- ------------------------------------------------------------------------
-- Identity laws
-- ------------------------------------------------------------------------

⇑τ-id : ∀ { n : ℕ } →  ((`_ { n }) ⇑τ)  ≡ `_ { n = 1 + n }
⇑τ-id = extensionality (lemma)
  where
    lemma : ∀ { n : ℕ } x →  ((`_ { n }) ⇑τ) x  ≡ ` x
    lemma zero = refl
    lemma (suc x) = refl


ren-τ-idᵣ : ∀ { n } → ren-τ (id { n }) ≡ Fun.id
ren-τ-idᵣ = extensionality lemma
  where
    lemma : ∀ { n } τ →  ren-τ (id { n }) τ ≡ τ
    lemma (` α) = refl
    lemma (τ₁ ⇒ τ₂) = ⇒-cong (lemma τ₁) (lemma τ₂)
    lemma (`∀ τ) = `∀-cong (
      begin 
        ren-τ (id ⇑) τ 
      ≡⟨ cong-app (ren-τ-cong ⇑-id) τ ⟩ 
        ren-τ id τ 
      ≡⟨ lemma τ ⟩ 
        τ 
      ∎)


sub-τ-idₗ : ∀ { m n } (σ : Sub (Type n) m) 
  → sub-τ σ ∘ `_  ≡ σ
sub-τ-idₗ σ = extensionality lemma
  where 
    lemma : ∀ x → sub-τ σ (` x) ≡ σ x
    lemma zero = refl
    lemma (suc x) = refl


-- The functional form of the Monad Law: Right Identity
sub-τ-idᵣ : ∀ { n } → sub-τ (`_ {n}) ≡ Fun.id
sub-τ-idᵣ = extensionality lemma
  where
    lemma : ∀ { n } τ → sub-τ (`_ {n}) τ ≡ τ
    lemma (` α) = refl
    lemma (τ₁ ⇒ τ₂) = ⇒-cong (lemma τ₁) (lemma τ₂)
    lemma (`∀ τ) = `∀-cong (
      begin 
        sub-τ ((`_) ⇑τ) τ 
      ≡⟨ cong-app (sub-τ-cong ⇑τ-id) τ ⟩ 
        sub-τ (`_) τ
      ≡⟨ lemma τ ⟩ 
        τ 
      ∎)


-- ------------------------------------------------------------------------
-- Monad Law : Compositionality
-- ------------------------------------------------------------------------
-- Lemmas required to prove the law:
-- sub-τ σ₂ ∘ sub-τ σ₁ ≡ sub-τ (sub-τ σ₂ ∘ σ₁)

∘-ren-τ-distrib : ∀ { m n k } ( ρ₁ : Ren m n ) ( ρ₂ : Ren n k )
  → ren-τ ρ₂ ∘ ren-τ ρ₁ ≡ ren-τ (ρ₂ ∘ ρ₁)
∘-ren-τ-distrib ρ₁ ρ₂ = extensionality (lemma ρ₁ ρ₂)
  where 
    lemma : ∀ { m n k } ( ρ₁ : Ren m n ) ( ρ₂ : Ren n k )
      → ∀ τ → ren-τ ρ₂ (ren-τ ρ₁ τ) ≡ ren-τ (ρ₂ ∘ ρ₁) τ
    lemma ρ₁ ρ₂ (` α) = refl
    lemma ρ₁ ρ₂ (τ₁ ⇒ τ₂) = ⇒-cong (lemma ρ₁ ρ₂ τ₁) (lemma ρ₁ ρ₂ τ₂)
    lemma ρ₁ ρ₂ (`∀ τ) = `∀-cong (
      begin 
        ren-τ (ρ₂ ⇑) (ren-τ (ρ₁ ⇑) τ) 
      ≡⟨ lemma (ρ₁ ⇑) (ρ₂ ⇑) τ ⟩ 
        ren-τ (ρ₂ ⇑ ∘ ρ₁ ⇑) τ 
      ≡⟨ cong-app (ren-τ-cong (∘-⇑-distrib ρ₁ ρ₂)) τ ⟩ 
        ren-τ ((ρ₂ ∘ ρ₁) ⇑) τ 
      ∎)

∘-⇑-ren-τ-distrib : ∀ { m n k } (σ : Sub (Type n) m) (ρ : Ren n k) 
  → ren-τ (ρ ⇑) ∘ (σ ⇑τ) ≡ (ren-τ ρ ∘ σ) ⇑τ
∘-⇑-ren-τ-distrib σ ρ = extensionality lemma
  where 
    lemma : ∀ x → ren-τ (ρ ⇑) ((σ ⇑τ) x) ≡ ((ren-τ ρ ∘ σ) ⇑τ) x
    lemma zero = refl
    lemma (suc x) = 
      begin
        ren-τ (ρ ⇑) ((σ ⇑τ) (suc x))
      ≡⟨⟩
        ren-τ (ρ ⇑) (ren-τ ↑ (σ x))
      ≡⟨ cong-app (∘-ren-τ-distrib ↑ (ρ ⇑)) (σ x) ⟩
        ren-τ (ρ ⇑ ∘ ↑) (σ x)
      ≡⟨ cong-app (sym (∘-ren-τ-distrib ρ ↑)) (σ x) ⟩
        ren-τ ↑ (ren-τ ρ (σ x))
      ≡⟨⟩
        ((ren-τ ρ ∘ σ) ⇑τ) (suc x)
      ∎

-- ∘-⇑✶-ren-τ-distrib

∘-⇑-τ-distrib : ∀  { m n k } (σ : Sub (Type k) n) (ρ : Ren m n)
  → (σ ⇑τ) ∘ (ρ ⇑) ≡ (σ ∘ ρ) ⇑τ
∘-⇑-τ-distrib σ ρ = extensionality lemma
  where
    lemma : ∀ x → (σ ⇑τ) ((ρ ⇑) x) ≡ ((σ ∘ ρ) ⇑τ) x
    lemma zero = refl
    lemma (suc x) = refl

∘-sub-ren-τ-distrib : ∀ { m n k } (σ : Sub (Type k) n) (ρ : Ren m n)
  → sub-τ σ ∘ ren-τ ρ ≡ sub-τ (σ ∘ ρ)
∘-sub-ren-τ-distrib σ ρ = extensionality (lemma σ ρ)
  where 
    lemma : ∀ { m n k } (σ : Sub (Type k) n) (ρ : Ren m n)
      → ∀ τ → sub-τ σ (ren-τ ρ τ) ≡ sub-τ (σ ∘ ρ) τ
    lemma σ ρ (` α) = refl
    lemma σ ρ (τ₁ ⇒ τ₂) = ⇒-cong (lemma σ ρ τ₁) (lemma σ ρ τ₂)
    lemma σ ρ (`∀ τ) = `∀-cong (
      begin
        sub-τ (σ ⇑τ) (ren-τ (ρ ⇑) τ)
      ≡⟨ lemma (σ ⇑τ) (ρ ⇑) τ ⟩ 
        sub-τ ((σ ⇑τ) ∘ (ρ ⇑)) τ
      ≡⟨ cong-app (sub-τ-cong (∘-⇑-τ-distrib σ ρ)) τ ⟩ 
        sub-τ ((σ ∘ ρ) ⇑τ) τ
      ∎)

∘-ren-sub-τ-distrib : ∀ { m n k } (σ : Sub (Type n) m) (ρ : Ren n k)
  → ren-τ ρ ∘ sub-τ σ ≡ sub-τ (ren-τ ρ ∘ σ) 
∘-ren-sub-τ-distrib σ ρ = extensionality (lemma σ ρ)
  where 
    lemma : ∀ { m n k } (σ : Sub (Type n) m) (ρ : Ren n k) 
      → ∀ τ → ren-τ ρ (sub-τ σ τ) ≡ sub-τ (ren-τ ρ ∘ σ) τ 
    lemma σ ρ (` α) = refl
    lemma σ ρ (τ₁ ⇒ τ₂) = ⇒-cong (lemma σ ρ τ₁) (lemma σ ρ τ₂)
    lemma σ ρ (`∀ τ) = `∀-cong (
      begin 
        ren-τ (ρ ⇑) (sub-τ (σ ⇑τ) τ)
      ≡⟨ lemma (σ ⇑τ) (ρ ⇑) τ ⟩ 
        sub-τ (ren-τ (ρ ⇑) ∘ (σ ⇑τ)) τ
      ≡⟨ cong-app (sub-τ-cong (∘-⇑-ren-τ-distrib σ ρ)) τ ⟩ 
        sub-τ ((ren-τ ρ ∘ σ) ⇑τ) τ
      ∎)


∘-⇑-sub-τ-distrib : ∀ { m n k } (σ₁ : Sub (Type n) m) (σ₂ : Sub (Type k) n)
  → sub-τ (σ₂ ⇑τ) ∘ σ₁ ⇑τ ≡ (sub-τ σ₂ ∘ σ₁) ⇑τ
∘-⇑-sub-τ-distrib σ₁ σ₂ = extensionality lemma
  where 
    lemma : ∀ x → sub-τ (σ₂ ⇑τ) ((σ₁ ⇑τ) x) ≡ ((sub-τ σ₂ ∘ σ₁) ⇑τ) x
    lemma zero = refl
    lemma (suc x) = 
      begin
        sub-τ (σ₂ ⇑τ) ((σ₁ ⇑τ) (suc x))
      ≡⟨⟩
        sub-τ (σ₂ ⇑τ) (ren-τ ↑ (σ₁ x))
      ≡⟨ cong-app (∘-sub-ren-τ-distrib (σ₂ ⇑τ) ↑) (σ₁ x) ⟩
        sub-τ ((σ₂ ⇑τ) ∘ ↑) (σ₁ x)
      ≡⟨⟩
        sub-τ (ren-τ ↑ ∘ σ₂) (σ₁ x)
      ≡⟨ cong-app (sym (∘-ren-sub-τ-distrib σ₂ ↑)) (σ₁ x) ⟩
        ren-τ ↑ (sub-τ σ₂ (σ₁ x))
      ≡⟨⟩ 
        ((sub-τ σ₂ ∘ σ₁) ⇑τ) (suc x)
      ∎

∘-sub-τ-distrib : ∀ { m n k } ( σ₁ : Sub (Type n) m ) ( σ₂ : Sub (Type k) n )
  → sub-τ σ₂ ∘ sub-τ σ₁ ≡ sub-τ (sub-τ σ₂ ∘ σ₁)
∘-sub-τ-distrib σ₁ σ₂ = extensionality (lemma σ₁ σ₂)
  where 
    lemma : ∀ { m n k } ( σ₁ : Sub (Type n) m ) ( σ₂ : Sub (Type k) n )
      → ∀ τ → sub-τ σ₂ (sub-τ σ₁ τ) ≡ sub-τ (sub-τ σ₂ ∘ σ₁) τ
    lemma σ₁ σ₂ (` α) = refl
    lemma σ₁ σ₂ (τ₁ ⇒ τ₂) = ⇒-cong (lemma σ₁ σ₂ τ₁) (lemma σ₁ σ₂ τ₂)
    lemma σ₁ σ₂ (`∀ τ) = `∀-cong (
      begin 
        sub-τ (σ₂ ⇑τ) (sub-τ (σ₁ ⇑τ) τ) 
      ≡⟨ lemma (σ₁ ⇑τ) (σ₂ ⇑τ) τ ⟩ 
        sub-τ (sub-τ (σ₂ ⇑τ) ∘ (σ₁ ⇑τ)) τ 
      ≡⟨ cong-app (sub-τ-cong (∘-⇑-sub-τ-distrib σ₁ σ₂)) τ ⟩ 
        sub-τ ((sub-τ σ₂ ∘ σ₁) ⇑τ) τ
      ∎)

-- ------------------------------------------------------------------------
-- Supplementary Laws
-- ------------------------------------------------------------------------

∘-sub-τ : ∀ { m n k l } ( σ₁ : Sub (Type n) m ) ( σ₂ : Sub (Type k) n ) (σ₃ : Sub (Type l) k)
  → sub-τ σ₃ ∘ (sub-τ σ₂ ∘ σ₁) ≡ sub-τ (sub-τ σ₃ ∘ σ₂) ∘ σ₁
∘-sub-τ σ₁ σ₂ σ₃ = 
  begin 
    sub-τ σ₃ ∘ (sub-τ σ₂ ∘ σ₁) 
  ≡⟨⟩ 
    (sub-τ σ₃ ∘ sub-τ σ₂) ∘ σ₁ 
  ≡⟨ cong (_∘ σ₁) (∘-sub-τ-distrib σ₂ σ₃) ⟩ 
    sub-τ (sub-τ σ₃ ∘ σ₂) ∘ σ₁ 
  ∎


-- ------------------------------------------------------------------------


-- infixl 7 _·_ _[_]
-- infix 9 #_

-- data Term (n : ℕ) (m : ℕ) : Set where
--   #_ : Fin n → Term n m
--   ƛ : Term (1 + n) m → Term n m
--   _·_ : Term n m → Term n m → Term n m
--   _[_] : Term n m → Type m → Term n m
--   Λ : Term n (1 + m) → Term n m 








