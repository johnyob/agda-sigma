module Sigma.Subst.Properties where

open import Data.Nat using (ℕ; _+_; zero; suc)
open import Data.Fin using (Fin; zero; suc)

open import Sigma.Subst.Core 
open import Sigma.Renaming.Base

open import Function using (_∘_)


open import Data.Product using (∃₂; _×_) renaming ( _,_ to ⟨_,_⟩ )

open import Relation.Binary.PropositionalEquality as Eq
  using (_≡_; refl; sym; trans; cong; cong₂; cong-app)
open Eq.≡-Reasoning

-- ------------------------------------------------------------------------

-- We require a restricted form of functional extensionality
-- to prove whether to subsitutions are equivalent

postulate 
  extensionality : ∀ { n } { T } { f g : Sub T n }
    → (∀ x → f x ≡ g x)
    → f ≡ g

-- ------------------------------------------------------------------------
-- Expansion law
-- ------------------------------------------------------------------------

expansion : ∀ { T } ( σ₁ σ₂ : Sub T 0 )
  → σ₁ ≡ σ₂
expansion σ₁ σ₂ = extensionality λ ()


-- ------------------------------------------------------------------------
-- ∷-laws
-- ------------------------------------------------------------------------
-- Also known as the Interaction laws

∷-cong : ∀ { n } { T } { x₁ x₂ : T } { σ₁ σ₂ : Sub T n }
  → x₁ ≡ x₂
  → σ₁ ≡ σ₂
  -- ----------------
  → x₁ ∷ σ₁ ≡ x₂ ∷ σ₂
∷-cong x₁≡x₂ σ₁≡σ₂ = cong₂ (_∷_) x₁≡x₂ σ₁≡σ₂

∷-head : ∀ { n } { T } { x : T } { σ : Sub T n }
  → head (x ∷ σ) ≡ x
∷-head = refl

∷-tail : ∀ { n } { T } { x : T } { σ : Sub T n } 
  → tail (x ∷ σ) ≡ σ
∷-tail = refl

∷-uncons : ∀ { n } { T } { x : T } { σ : Sub T n } 
  → uncons (x ∷ σ) ≡ ⟨ x , σ ⟩
∷-uncons = refl

∷-head-tail-id : ∀ { n } { T } ( σ : Sub T (1 + n) ) 
  → head σ ∷ tail σ ≡ σ
∷-head-tail-id σ = extensionality lemma
  where 
    lemma : ∀ x → (head σ ∷ tail σ) x ≡ σ x
    lemma zero = refl
    lemma (suc x) = refl

∷-id-η : ∀ { n } → ( zero ∷ ↑ ) ≡ id { n = 1 + n }
∷-id-η = ∷-head-tail-id id

∷-∘-distrib : ∀ { n } { T U } { x : T } ( σ : Sub T n ) ( f : T → U ) 
  → f ∘ ( x ∷ σ ) ≡ f x ∷ f ∘ σ
∷-∘-distrib { x = x } σ f = extensionality lemma
  where
    lemma : ∀ y → (f ∘ (x ∷ σ)) y ≡ ( f x ∷ (f ∘ σ) ) y
    lemma zero = refl
    lemma (suc y) = refl

∃-split : ∀ { n } { T } ( σ₁ : Sub T (1 + n) )
  → ∃₂ λ ( x : T ) ( σ₂ : Sub T n ) → σ₁ ≡ x ∷ σ₂
∃-split σ = ⟨ head σ , ⟨ tail σ , sym (∷-head-tail-id σ) ⟩ ⟩

-- TODO: Prove these. 
-- x₁ ≡ head (x₁ ∷ σ₁) ::-head
--    ≡ head (x₂ ∷ σ₂) cong
--    ≡ x₂             ::-head

postulate
  ∷-injectiveˡ : ∀ { n } { T } ( x₁ x₂ : T ) ( σ₁ σ₂ : Sub T n ) 
    → x₁ ∷ σ₁ ≡ x₁ ∷ σ₂ → x₁ ≡ x₂

  ∷-injectiveʳ : ∀ { n } { T } ( x₁ x₂ : T ) ( σ₁ σ₂ : Sub T n ) 
    → x₁ ∷ σ₁ ≡ x₁ ∷ σ₂ → σ₁ ≡ σ₂


∷-injective : ∀ { n } { T } ( x₁ x₂ : T ) ( σ₁ σ₂ : Sub T n ) 
  → x₁ ∷ σ₁ ≡ x₁ ∷ σ₂ → (x₁ ≡ x₂) × (σ₁ ≡ σ₂)
∷-injective x₁ x₂ σ₁ σ₂ x₁∷σ₁≡x₁∷σ₂ = ⟨ (∷-injectiveˡ x₁ x₂ σ₁ σ₂ x₁∷σ₁≡x₁∷σ₂) , (∷-injectiveʳ x₁ x₂ σ₁ σ₂ x₁∷σ₁≡x₁∷σ₂) ⟩


-- ------------------------------------------------------------------------
-- Coincidence laws
-- ------------------------------------------------------------------------
-- Equivalences between uni and multi-variate primitives

++-∷ : ∀ { n } { T } (x : T) (σ : Sub T n)
  → x ∷ σ ≡ [ x ] ++ σ
++-∷ x σ = refl

-- ------------------------------------------------------------------------
-- Multi-variate interaction laws
-- ------------------------------------------------------------------------

++-cong : ∀ { m n } { T } {σ₁¹ σ₁² : Sub T m} {σ₂¹ σ₂² : Sub T n}
  → σ₁¹ ≡ σ₁²
  → σ₂¹ ≡ σ₂²
  -- -----------------------
  → σ₁¹ ++ σ₂¹ ≡ σ₁² ++ σ₂²
++-cong refl refl = refl

-- TODO: ++-injective 
-- TODO: ++-≥ and ++-<

∷-drop : ∀ { m n } { T } (x : T) (σ : Sub T (m + n))
  → drop (suc m) (x ∷ σ) ≡ drop m σ
∷-drop x σ = extensionality (lemma x σ)
  where
    lemma : ∀ { m n } { T } (x : T) (σ : Sub T (m + n))
      → ∀ y → drop (suc m) (x ∷ σ) y ≡ drop m σ y
    lemma {zero} x σ y = refl
    lemma {suc m} x σ y = refl

++-drop : ∀ { m n : ℕ } { T } (σ₁ : Sub T m) (σ₂ : Sub T n)
  → drop m (σ₁ ++ σ₂) ≡ σ₂ 
++-drop σ₁ σ₂ = extensionality (lemma σ₁ σ₂)
  where 
    lemma : ∀ { m n } { T } (σ₁ : Sub T m) (σ₂ : Sub T n)
      → ∀ x → drop m (σ₁ ++ σ₂) x ≡ σ₂ x
    lemma {zero} σ₁ σ₂ x = refl
    lemma {suc m} σ₁ σ₂ x = lemma (σ₁ ∘ ↑) σ₂ x

∷-take : ∀ { m n } { T } (x : T) (σ : Sub T (m + n))
  → take (suc m) (x ∷ σ) ≡ x ∷ take m σ
∷-take x σ = extensionality (lemma x σ)
  where
    lemma : ∀ { m n } { T } (x : T) (σ : Sub T (m + n))
      → ∀ y → take (suc m) (x ∷ σ) y ≡ (x ∷ take m σ) y
    lemma x σ zero = refl
    lemma x σ (suc y) = refl

++-take : ∀ { m n } { T } (σ₁ : Sub T m) (σ₂ : Sub T n)
  → take m (σ₁ ++ σ₂) ≡ σ₁ 
++-take σ₁ σ₂ = extensionality (lemma σ₁ σ₂)
  where
    lemma : ∀ { m n } { T } (σ₁ : Sub T m) (σ₂ : Sub T n)
      → ∀ x → take m (σ₁ ++ σ₂) x ≡ σ₁ x
    lemma σ₁ σ₂ zero = refl
    lemma σ₁ σ₂ (suc x) = lemma (σ₁ ∘ ↑) σ₂ x


++-take-drop-id : ∀ m { n } { T } (σ : Sub T (m + n))
  → take m σ ++ drop m σ ≡ σ
++-take-drop-id m σ = extensionality (lemma m σ)
  where 
    lemma : ∀ m { n } { T } (σ : Sub T (m + n))
      → ∀ x → (take m σ ++ drop m σ) x ≡ σ x
    lemma zero σ x = refl
    lemma (suc m) σ zero = refl
    lemma (suc m) σ (suc x) = lemma m (σ ∘ ↑) x


∃-splitAt : ∀ m { n } { T } ( σ : Sub T (m + n) ) 
  → ∃₂ λ ( σ₁ : Sub T m ) ( σ₂ : Sub T n ) → σ ≡ σ₁ ++ σ₂
∃-splitAt m σ = ⟨ take m σ , ⟨ drop m σ , sym (++-take-drop-id m σ) ⟩ ⟩


take-∘-distrib : ∀ m { n } { T U } (σ : Sub T (m + n)) (f : T → U)
  → take m (f ∘ σ) ≡ f ∘ (take m σ)
take-∘-distrib m σ f = extensionality (lemma m σ f)
  where
    lemma : ∀ m { n } { T U } (σ : Sub T (m + n)) (f : T → U)
      → ∀ x → take m (f ∘ σ) x ≡ (f ∘ (take m σ)) x
    lemma .(suc _) σ f zero = refl
    lemma .(suc _) σ f (suc x) = refl


drop-∘-distrib : ∀ m { n } { T U } (σ : Sub T (m + n)) (f : T → U)
  → drop m (f ∘ σ) ≡ f ∘ (drop m σ)
drop-∘-distrib m σ f = extensionality (lemma m σ f)
  where
    lemma : ∀ m { n } { T U } (σ : Sub T (m + n)) (f : T → U)
      → ∀ x → drop m (f ∘ σ) x ≡ (f ∘ (drop m σ)) x
    lemma zero σ f x = refl
    lemma (suc m) σ f x = refl

++-∘-distrib : ∀ { m n } { T U } (σ₁ : Sub T m) (σ₂ : Sub T n) (f : T → U)
  → f ∘ ( σ₁ ++ σ₂ ) ≡ (f ∘ σ₁) ++ (f ∘ σ₂)
++-∘-distrib { m } σ₁ σ₂ f =  
  let σ = σ₁ ++ σ₂ in 
  begin
    f ∘ σ
  ≡⟨ sym (++-take-drop-id m (f ∘ σ)) ⟩
    take m (f ∘ σ) ++ drop m (f ∘ σ)
  ≡⟨ cong₂ _++_ (take-∘-distrib m σ f) (drop-∘-distrib m σ f) ⟩
    f ∘ (take m σ) ++ f ∘ (drop m σ)
  ≡⟨ cong₂ (λ σ₁ σ₂ → f ∘ σ₁ ++ f ∘ σ₂) (++-take σ₁ σ₂) (++-drop σ₁ σ₂) ⟩
    (f ∘ σ₁) ++ (f ∘ σ₂)
  ∎
  
-- ------------------------------------------------------------------------
-- Sub↔Vec
-- ------------------------------------------------------------------------
-- TODO