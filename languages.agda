open import Data.Bool hiding (T)
open import Relation.Nullary
open import Data.Nat
open import Data.Product

open import language
open import theorems

module languages where

module Arithmetic where
  data E : Set where
    ⌜_⌝ : ℕ → E
    _⊕_ : E → E → E

  infixr 1 _⇒_
    
  data _⇒_ : E → E → Set where
    contraction : ∀ n m → ⌜ n ⌝ ⊕ ⌜ m ⌝ ⇒ ⌜ n + m ⌝
    congruence1 : ∀ {e₁ e₁' e₂} → e₁ ⇒ e₁' → e₁ ⊕ e₂ ⇒ e₁' ⊕ e₂
    congruence2 : ∀ {e₁ e₂ e₂'} → e₂ ⇒ e₂' → e₁ ⊕ e₂ ⇒ e₁ ⊕ e₂'

  data T : Set where
    Nat : T

  data V : Set where -- empty set of variables
  data Γ : Set where -- empty context

  infixr 1 _⊢_∷_

  data _⊢_∷_ : Γ → E → T → Set where
    literal  : ∀ {n Γ} →  Γ ⊢ ⌜ n ⌝ ∷ Nat
    addition : ∀ {e₁ e₂ Γ} → Γ ⊢ e₁ ∷ Nat → Γ ⊢ e₂ ∷ Nat → Γ ⊢ e₁ ⊕ e₂ ∷ Nat

  arithmetic : Language
  arithmetic = record
               { E = E
               ; _⇒_ = _⇒_
               ; T = T
               ; V = V
               ; Γ = Γ
               ; _⊢_∷_ = _⊢_∷_
               }

  module SubjectExpansionProof where
    open SubjectExpansion arithmetic

    proof : subjectexpansion
    proof (contraction n m) literal = addition literal literal
    proof (congruence1 e⇒e') (addition e₁∷Nat e₂∷Nat) = addition (proof e⇒e' e₁∷Nat) e₂∷Nat
    proof (congruence2 e⇒e') (addition e₁∷Nat e₂∷Nat) = addition e₁∷Nat (proof e⇒e' e₂∷Nat)


module TypedLambdaCalculus where

  V : Set
  V = ℕ

  data T : Set where
    Nat : T
    _⟶_ : T → T → T 

  data E : Set where
    num : ℕ → E -- numbers
    var : V → E -- variables
    _∙_ : E → E → E -- application
    Λ_∷_,_ : V → T → E → E -- abstraction; λ is a reserved word, therefore we use Λ

  _==_ : ℕ → ℕ → Bool
  zero == zero = true
  zero == suc n₂ = false
  suc n₁ == zero = false
  suc n₁ == suc n₂ = n₁ == n₂ 

  _[_/_] : E → V → E → E
  (num x)[ v / s ] = num x
  (var x)[ v / s ] = if x == v then s else var x
  (e₁ ∙ e₂)[ v / s ] = e₁ [ v / s ] ∙ e₂ [ v / s ]
  (Λ y ∷ T , e) [ x / s ] = Λ y ∷ T , e [ x / s ] -- TODO check for x ≠ y and y ∉ FV(s)

  infixr 1 _⇒_
  
  data _⇒_ : E → E → Set where
    contraction : ∀ {e₁ e₂ x T} → (Λ x ∷ T , e₁) ∙ e₂ ⇒ e₁ [ x / e₂ ]
    congruence1 : ∀ {e₁ e₁' e₂} → e₁ ⇒ e₁' → e₁ ∙ e₂ ⇒ e₁' ∙ e₂
    congruence2 : ∀ {e₁ e₂ e₂'} → e₂ ⇒ e₂' → e₁ ∙ e₂ ⇒ e₁ ∙ e₂'

  data Γ : Set where
    ∅ : Γ
    _,_∷_ : Γ → V → T → Γ

  data _∈_ : V × T → Γ → Set where
    yes : ∀ {x T Γ'} → (x , T) ∈ (Γ' , x ∷ T)

  data _⊢_∷_ : Γ → E → T → Set where
    num : ∀ {n Γ} → Γ ⊢ num n ∷ Nat
    var : ∀ {x T Γ} → (x , T) ∈ Γ → Γ ⊢ var x ∷ T
    abs : ∀ {x t₂ Γ T₁ T₂} → (Γ , x ∷ T₁) ⊢ t₂ ∷ T₂ → Γ ⊢ (Λ x ∷ T₁ , t₂) ∷ (T₁ ⟶ T₂)
    app : ∀ {t₁ t₂ T₁ T₂ Γ} → Γ ⊢ t₁ ∷ (T₁ ⟶ T₂) → Γ ⊢ t₂ ∷ T₁ → Γ ⊢ t₁ ∙ t₂ ∷ T₂

  typedLambdaCalculus : Language
  typedLambdaCalculus = record
               { E = E
               ; _⇒_ = _⇒_
               ; T = T
               ; V = V
               ; Γ = Γ
               ; _⊢_∷_ = _⊢_∷_
               }

  module SubjectExpansionProof where
    open SubjectExpansion typedLambdaCalculus

    e⇒e' : (Λ 1 ∷ Nat , num 1) ∙ (num 1 ∙ num 1) ⇒ num 1
    e⇒e' = contraction

    e'∷Nat : ∅ ⊢ num 1 ∷ Nat
    e'∷Nat = num

    proof : ¬ subjectexpansion
    proof f with f e⇒e' e'∷Nat
    proof f | app (abs num) (app () num)
