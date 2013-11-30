open import Data.Bool hiding (T)
open import Relation.Nullary
open import Data.Nat
open import Data.Product
open import Data.Char
open import Data.List

open import language
open import theorems
open import helper


module languages.untypedLambdaCalculus where
  V : Set
  V = Char

  data E : Set where
    ⌜_⌝ : ℕ → E -- numbers
    var : V → E -- variables
    _∙_ : E → E → E -- application
    Λ_,_ : V → E → E -- abstraction; λ is a reserved word, therefore we use Λ

  data Val : E → Set where
    num : ∀ {n} → Val ⌜ n ⌝
    abs : ∀ {x e} → Val (Λ x , e)

  FV : E → List Char
  FV ⌜ n ⌝ = []
  FV (var x) = [ x ]
  FV (e₁ ∙ e₂) = (FV e₁) ++ (FV e₂) 
  FV (Λ x , e) = delete x (FV e)

  _[_/_] : E → V → E → E
  ⌜ x ⌝ [ v / s ] = ⌜ x ⌝
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
               ; Val = Val
               ; _⇒_ = _⇒_
               ; V = V
               }

