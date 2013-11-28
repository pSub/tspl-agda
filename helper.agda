open import Data.Bool
open import Data.Nat

module helper where

  _==_ : ℕ → ℕ → Bool
  zero == zero = true
  zero == suc n₂ = false
  suc n₁ == zero = false
  suc n₁ == suc n₂ = n₁ == n₂

  _/=_ : ℕ → ℕ → Bool
  n /= m = not (n == m)
