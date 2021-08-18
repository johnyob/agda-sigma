module Sigma.Renaming.Vec where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Fin as Fin using (Fin; zero; suc)

open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)

open import Data.Vec as V using (Vec; []; _∷_; map; _[_]≔_)
  renaming (head to headᵥ; tail to tailᵥ; lookup to lookupᵥ; insert to insertᵥ; remove to removeᵥ; updateAt to updateAtᵥ)
open import Data.HVec as HV using (HVec; []; _∷_)
  renaming (head to headₕ; tail to tailₕ; lookup to lookupₕ; insert to insertₕ; remove to removeₕ; updateAt to updateAtₕ)

open import Function as Fun using (_∘_)

open import Sigma.Renaming.Base as R using (Ren) 
  renaming (id to idᵣ; ↑ to ↑ᵣ; _⇑ to _⇑ᵣ)


open import Relation.Binary.PropositionalEquality as Eq
  using (_≡_; refl; sym; trans; cong; cong₂; cong-app; subst)
open Eq.≡-Reasoning


-- ------------------------------------------------------------------------
-- Vectored Renaming Shape

-- A renaming ρ : 𝕀ᵐ → 𝕀ⁿ is defined by a *shape*, denoted m ↦ n. 
-- 
-- Similarly, a vectored renaming ρs = [ρ₁ ; ...; ρₖ] : [𝕀ᵐ₁ → 𝕀ⁿ₁, ...; 𝕀ᵐₖ → 𝕀ⁿₖ] 
-- is defined by a vector of renaming shapes, denoted [m₁ ↦ n₁; ...; mₖ ↦ nₖ]

module Shape where

  open import Data.Vec using (lookup; replicate; _[_]%=_; _[_]≔_)

  -- TODO: Implement shape for renaming?

  Shape : ℕ → Set
  Shape n = Vec (ℕ × ℕ) n

  -- -------------------------------------------

  pattern _↦_ m n = ⟨ m , n ⟩

  shape : ∀ { n } → Shape n → Fin n → ℕ × ℕ
  shape = lookup

  dom : ∀ { n } → Shape n → Fin n → ℕ
  dom s = proj₁ ∘ (shape s)

  rng : ∀ { n } → Shape n → Fin n → ℕ
  rng s = proj₂ ∘ (shape s)
  
  -- -------------------------------------------

  id : ∀ { m } → ℕ → Shape m
  id n = replicate (n ↦ n)

  ↑ : ∀ { m } → ℕ → Fin m → Shape m
  ↑ n i = id n [ i ]≔ n ↦ (1 + n)

  -- TODO: This may become a pain, used a hack to use := instead of
  -- %= 
  infix 10 _⇑_
  _⇑_ : ∀ { n } → Shape n → Fin n → Shape n
  s ⇑ i = s [ i ]≔ ⇑ (lookup s i)
    where 
      ⇑ : ℕ × ℕ → ℕ × ℕ
      ⇑ (m ↦ n) = (1 + m) ↦ (1 + n)

open Shape using (Shape; _↦_) renaming (id to idₛ; ↑ to ↑ₛ; _⇑_ to _⇑ₛ_)

-- TODO: Move this when implementing shapes on renamings?
-- IDEA: Call it an interpretation of a shape
-- use the nice brackets ;)

⦅_⦆ : ℕ × ℕ → Set
⦅ m ↦ n ⦆ = Ren m n

-- ------------------------------------------------------------------------
-- Vectored Renaming

-- A vectored renaming ρs = [ρ₁ ; ...; ρₖ] : [𝕀ᵐ₁ → 𝕀ⁿ₁, ...; 𝕀ᵐₖ → 𝕀ⁿₖ] 
-- defined by it's shape: [m₁ ↦ n₁; ...; mₖ ↦ nₖ]
-- It is implemented as a hetrogenous vector. 

VRen : ∀ n → Shape n → Set
VRen n shape = HVec n (map ⦅_⦆ shape)

length : ∀ { n S } → VRen n S → ℕ
length { n = n } _ = n

shape : ∀ { n S } → VRen n S → Shape n
shape { S = shape } _ = shape

-- ------------------------------------------------------------------------
-- Basic operations (ported from HVec)

-- Anonymous module containing properties about 
-- Data.Vec's map composed w/ other operations 
module _ { ℓ₁ ℓ₂ } { A : Set ℓ₁ } { B : Set ℓ₂ } where
  open import Data.Vec using (head; tail; insert; remove)

  private
    variable
      m n k : ℕ

  open import Data.Vec.Properties using (lookup-map; map-[]≔) public

  unfold-map : (f : A → B) (x : A) (xs : Vec A n) 
    → map f (x ∷ xs) ≡ f x ∷ map f xs
  unfold-map f x [] = refl
  unfold-map f x (_ ∷ xs) = refl

  unfold-remove : (x : A) (xs : Vec A (1 + n)) (i : Fin (1 + n))
    → remove (x ∷ xs) (suc i) ≡ x ∷ remove xs i 
  unfold-remove x (_ ∷ xs) zero = refl
  unfold-remove x (y ∷ xs) (suc i) = refl

  head-map : (f : A → B) (xs : Vec A (1 + n))
    → head (map f xs) ≡ f (head xs)
  head-map f (x ∷ xs) = refl

  tail-map : (f : A → B) (xs : Vec A (1 + n))
    → tail (map f xs) ≡ map f (tail xs)
  tail-map f (x ∷ xs) = refl

  insert-map : (f : A → B) (x : A) (xs : Vec A n) (i : Fin (1 + n)) 
    → insert (map f xs) i (f x) ≡ map f (insert xs i x)
  insert-map f x xs zero = refl
  insert-map f x (_ ∷ xs) (suc i) rewrite insert-map f x xs i = refl
  
  remove-map : (f : A → B) (xs : Vec A (1 + n)) (i : Fin (1 + n)) 
    → remove (map f xs) i ≡ map f (remove xs i)
  remove-map f (_ ∷ xs) zero = refl
  remove-map f (x ∷ y ∷ xs) (suc i) rewrite remove-map f (y ∷ xs) i = refl

module _ where

  private
    variable
      m n k : ℕ
      S : Shape m

  head : VRen (1 + m) S → ⦅ headᵥ S ⦆
  head ρs rewrite sym (head-map ⦅_⦆ (shape ρs)) = headₕ ρs
  
  tail : VRen (1 + m) S → VRen m (tailᵥ S)
  tail ρs rewrite sym (tail-map ⦅_⦆ (shape ρs)) = tailₕ ρs

  lookup : VRen m S → (i : Fin m) → ⦅ lookupᵥ S i ⦆
  lookup ρs i rewrite sym (lookup-map i ⦅_⦆ (shape ρs)) = lookupₕ ρs i

  insert : VRen m S → (i : Fin (1 + m)) → Ren n k → VRen (1 + m) (insertᵥ S i (n ↦ k))
  insert { n = n } { k = k } ρs i ρ rewrite sym (insert-map ⦅_⦆ (n ↦ k) (shape ρs) i) = insertₕ ρs i ρ

  remove : VRen (1 + m) S → (i : Fin (1 + m)) → VRen m (removeᵥ S i)
  remove ρs i rewrite sym (remove-map ⦅_⦆ (shape ρs) i) = removeₕ ρs i

  updateAt : (i : Fin m) → (⦅ lookupᵥ S i ⦆ → Ren n k) → VRen m S → VRen m (S [ i ]≔ n ↦ k)
  updateAt { n = n } { k = k } i f ρs rewrite map-[]≔ ⦅_⦆ (shape ρs) i { x = n ↦ k } = updateAtₕ i f' ρs
    where 
      f' : lookupᵥ (map ⦅_⦆ (shape ρs)) i → Ren n k 
      f' rewrite lookup-map i ⦅_⦆ (shape ρs) = f

  infixl 6 _[_]$=_

  _[_]$=_ : VRen m S → (i : Fin m) → (⦅ lookupᵥ S i ⦆ → Ren n k) → VRen m (S [ i ]≔ n ↦ k)
  ρs [ i ]$= f = updateAt i f ρs

  infixl 6 _[_]&=_

  _[_]&=_ : VRen m S → (i : Fin m) → Ren n k → VRen m (S [ i ]≔ n ↦ k)
  ρs [ i ]&= ρ = ρs [ i ]$= Fun.const ρ
  
-- ------------------------------------------------------------------------
-- Primitives

id : ∀ m { n } → VRen m (idₛ n)
id zero = []
id (suc m) = idᵣ ∷ id m

↑ : ∀ m { n } → (i : Fin m) → VRen m (↑ₛ n i)
↑ m i = (id m) [ i ]&= ↑ᵣ

_⇑_ : ∀ { n S } → VRen n S → (i : Fin n) → VRen n (S ⇑ₛ i)
ρs ⇑ i = ρs [ i ]$= (_⇑ᵣ)

-- ------------------------------------------------------------------------
