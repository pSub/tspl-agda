open import Data.Bool hiding (T)
open import Relation.Nullary
open import Data.Nat
open import Data.Product

open import language
open import theorems


module languages.typedLambdaCalculus where

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

  _/=_ : ℕ → ℕ → Bool
  n /= m = not (n == m)

  import Data.Nat.Properties
  open import Relation.Binary using (module StrictTotalOrder)
  open import Data.AVL.Sets (StrictTotalOrder.isStrictTotalOrder Data.Nat.Properties.strictTotalOrder)
  
  FV : E → ⟨Set⟩
  FV (num x) = empty
  FV (var x) = singleton x
  FV (e₁ ∙ e₂) = union (FV e₁) (FV e₂) 
  FV (Λ x ∷ T , e) = delete x (FV e)

  _[_/_] : E → V → E → E
  (num x)[ v / s ] = num x
  (var x)[ v / s ] = if x == v then s else var x
  (e₁ ∙ e₂)[ v / s ] = e₁ [ v / s ] ∙ e₂ [ v / s ]
  (Λ y ∷ T , e) [ x / s ] = if x /= y ∧ y ∈? (FV s)
                            then Λ y ∷ T , e [ x / s ]
                            else Λ y ∷ T , e

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

  language : TypedLanguage
  language = record
               { E = E
               ; _⇒_ = _⇒_
               ; T = T
               ; V = V
               ; Γ = Γ
               ; _⊢_∷_ = _⊢_∷_
               }

  module SubjectExpansionProof where
    open SubjectExpansion language

    e⇒e' : (Λ 1 ∷ Nat , num 1) ∙ (num 1 ∙ num 1) ⇒ num 1
    e⇒e' = contraction

    e'∷Nat : ∅ ⊢ num 1 ∷ Nat
    e'∷Nat = num

    proof : ¬ subjectexpansion
    proof f with f e⇒e' e'∷Nat
    proof f | app (abs num) (app () num)
