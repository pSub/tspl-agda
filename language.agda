open import Data.Nat

module language where

record Language : Set₁ where
  infixr 1 _⇒_
  field
    E     : Set -- expressions
    _⇒_   : E → E → Set -- reduction relation
    T     : Set -- types
    V     : Set -- variables
    Γ     : Set -- context
    _⊢_∷_ : Γ → E → T → Set -- type rules

