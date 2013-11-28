open import Data.Bool hiding (T)
open import Relation.Nullary
open import Data.Nat
open import Data.Product

open import language
open import theorems
open import helper


module languages.untypedLambdaCalculus where

  V : Set
  V = ℕ

  data E : Set where
    num : ℕ → E -- numbers
    var : V → E -- variables
    _∙_ : E → E → E -- application
    Λ_,_ : V → E → E -- abstraction; λ is a reserved word, therefore we use Λ

  import Data.Nat.Properties
  open import Relation.Binary using (module StrictTotalOrder)
  open import Data.AVL.Sets (StrictTotalOrder.isStrictTotalOrder Data.Nat.Properties.strictTotalOrder)
  
  FV : E → ⟨Set⟩
  FV (num x) = empty
  FV (var x) = singleton x
  FV (e₁ ∙ e₂) = union (FV e₁) (FV e₂) 
  FV (Λ x , e) = delete x (FV e)

  _[_/_] : E → V → E → E
  (num x)[ v / s ] = num x
  (var x)[ v / s ] = if x == v then s else var x
  (e₁ ∙ e₂)[ v / s ] = e₁ [ v / s ] ∙ e₂ [ v / s ]
  (Λ y , e) [ x / s ] = if x /= y ∧ not (y ∈? (FV s))
                            then Λ y , e [ x / s ]
                            else Λ y , e

  infixr 1 _⇒_
  
  data _⇒_ : E → E → Set where
    contraction : ∀ {e₁ e₂ x} → (Λ x , e₁) ∙ e₂ ⇒ e₁ [ x / e₂ ]
    congruence1 : ∀ {e₁ e₁' e₂} → e₁ ⇒ e₁' → e₁ ∙ e₂ ⇒ e₁' ∙ e₂
    congruence2 : ∀ {e₁ e₂ e₂'} → e₂ ⇒ e₂' → e₁ ∙ e₂ ⇒ e₁ ∙ e₂'
  
  language : UntypedLanguage
  language = record
               { E = E
               ; _⇒_ = _⇒_
               ; V = V
               }
