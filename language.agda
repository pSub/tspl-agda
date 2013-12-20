open import Data.Nat

module language where

record TypedLanguage : Set₁ where
  infixr 1 _⇒_
  field
    E     : Set -- expressions
    Val   : E → Set -- values
    _⇒_   : E → E → Set -- reduction relation
    T     : Set -- types
    V     : Set -- variables
    Γ     : Set -- context
    ∅     : Γ   -- empty context
    _,_∷_ : Γ → V → T → Γ -- variable in context
    _⊢_∷_ : Γ → E → T → Set -- type rules

record UntypedLanguage : Set₁ where
  infixr 1 _⇒_
  field
    E     : Set -- expressions
    Val   : E → Set -- values
    _⇒_   : E → E → Set -- reduction relation
    V     : Set -- variables

