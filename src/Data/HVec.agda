module Data.HVec where

open import Data.Fin using (Fin; zero; suc)
open import Data.Nat using (ℕ; zero; suc; _+_)

open import Function using (const)

open import Data.Vec as V using (Vec; []; _∷_; _[_]≔_)

open import Level as L using (Level; suc)


-- ------------------------------------------------------------------------
-- Hetrogenous Vectors

infixr 5 _∷_

data HVec { ℓ } : ( n : ℕ ) → Vec (Set ℓ) n → Set ℓ where
  [] : HVec 0 []
  _∷_ : ∀ { n } { A : Set ℓ } { As }
    → A
    → HVec n As
    -- ----------------------
    → HVec (1 + n) (A ∷ As) 

-- -- ------------------------------------------------------------------------

private
  variable
    ℓ : Level
    A : Set ℓ
    n : ℕ
    As : Vec (Set ℓ) n


length : HVec n As → ℕ
length { n = n } _ = n

head : HVec (1 + n) As → (V.head As)
head (x ∷ xs) = x

tail : HVec (1 + n) As → HVec n (V.tail As)
tail (x ∷ xs) = xs

lookup : HVec n As → (i : Fin n) → (V.lookup As i)
lookup (x ∷ xs) zero = x
lookup (x ∷ xs) (suc i) = lookup xs i

insert : HVec n As → (i : Fin (1 + n)) → A → HVec (1 + n) (V.insert As i A)
insert xs zero v = v ∷ xs
insert (x ∷ xs) (suc i) v = x ∷ insert xs i v

remove : HVec (1 + n) As → (i : Fin (1 + n)) → HVec n (V.remove As i)
remove (x ∷ xs) zero = xs
remove (x₁ ∷ x₂ ∷ xs) (suc i) = x₁ ∷ remove (x₂ ∷ xs) i

updateAt : ∀ { ℓ n } { A : Set ℓ } { As : Vec (Set ℓ) n } (i : Fin n) → (V.lookup As i → A) → HVec n As → HVec n (As [ i ]≔ A)
updateAt zero f (x ∷ xs) = f x ∷ xs
updateAt (suc i) f (x ∷ xs) = x ∷ updateAt i f xs

infixl 6 _[_]$=_

_[_]$=_ : HVec n As → (i : Fin n) → (V.lookup As i → A) → HVec n (As [ i ]≔ A)
xs [ i ]$= f = updateAt i f xs

infixl 6 _[_]&=_

_[_]&=_ : HVec n As → (i : Fin n) → A → HVec n (As [ i ]≔ A)
xs [ i ]&= y = xs [ i ]$= const y

-- -- ------------------------------------------------------------------------

