open import Data.Bool
open import Data.Nat
open import Data.List
open import Data.Char

module helper where

  _/=_ : Char → Char → Bool
  n /= m = not (n == m)

  delete : Char → List Char → List Char
  delete a [] = []
  delete a (x ∷ xs) = if a == x then delete a xs else x ∷ delete a xs

  _∈?_ : Char → List Char → Bool
  a ∈? [] = false
  a ∈? (x ∷ xs) = (a == x) ∨ (a ∈? xs)
