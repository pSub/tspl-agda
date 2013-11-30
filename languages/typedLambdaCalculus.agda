open import Data.Bool hiding (T)
open import Relation.Nullary
open import Data.Nat
open import Data.Char
open import Data.Sum
open import Data.Product
open import Data.List renaming (_∷_ to cons)

open import language
open import theorems
open import helper

module languages.typedLambdaCalculus where
  V : Set
  V = Char

  data T : Set where
    Nat : T
    _⟶_ : T → T → T 

  data E : Set where
    ⌜_⌝ : ℕ → E -- numbers
    var : V → E -- variables
    _∙_ : E → E → E -- application
    Λ_∷_,_ : V → T → E → E -- abstraction; λ is a reserved word, therefore we use Λ

  data Val : E → Set where
    num : ∀ {n} → Val ⌜ n ⌝
    abs : ∀ {x T e} → Val (Λ x ∷ T , e)
  
  FV : E → List Char
  FV ⌜ x ⌝ = []
  FV (var x) = [ x ]
  FV (e₁ ∙ e₂) = (FV e₁) ++ (FV e₂) 
  FV (Λ x ∷ T , e) = delete x (FV e)

  _[_/_] : E → V → E → E
  ⌜ x ⌝ [ v / s ] = ⌜ x ⌝
  (var x)[ v / s ] = if x == v then s else var x
  (e₁ ∙ e₂)[ v / s ] = e₁ [ v / s ] ∙ e₂ [ v / s ]
  (Λ y ∷ T , e) [ x / s ] = if x /= y ∧ not (y ∈? (FV s))
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
    num : ∀ {n Γ} → Γ ⊢ ⌜ n ⌝ ∷ Nat
    var : ∀ {x T Γ} → (x , T) ∈ Γ → Γ ⊢ var x ∷ T
    abs : ∀ {x t₂ Γ T₁ T₂} → (Γ , x ∷ T₁) ⊢ t₂ ∷ T₂ → Γ ⊢ (Λ x ∷ T₁ , t₂) ∷ (T₁ ⟶ T₂)
    app : ∀ {t₁ t₂ T₁ T₂ Γ} → Γ ⊢ t₁ ∷ (T₁ ⟶ T₂) → Γ ⊢ t₂ ∷ T₁ → Γ ⊢ t₁ ∙ t₂ ∷ T₂

  language : TypedLanguage
  language = record
               { E = E
               ; Val = Val
               ; _⇒_ = _⇒_
               ; T = T
               ; V = V
               ; Γ = Γ
               ; ∅ = ∅
               ; _⊢_∷_ = _⊢_∷_
               }

  module SubjectExpansionProof where
    open SubjectExpansion language

    e⇒e' : (Λ 'x' ∷ Nat , ⌜ 1 ⌝) ∙ (⌜ 1 ⌝ ∙ ⌜ 1 ⌝) ⇒ ⌜ 1 ⌝
    e⇒e' = contraction

    e'∷Nat : ∅ ⊢ ⌜ 1 ⌝ ∷ Nat
    e'∷Nat = num

    proof : ¬ subjectexpansion
    proof f with f e⇒e' e'∷Nat
    proof f | app (abs num) (app () num)

  module ProgressProof where
    open Progress language

    proof : progress
    proof (num {n}) = ⌜ n ⌝ , inj₂ num
    proof (var ())
    proof (abs {x} {e} {.∅} {T} e∷T) = (Λ x ∷ T , e) , inj₂ abs
    proof (app {⌜ n ⌝} () e₂∷T)
    proof (app {var x} (var ()) e₂∷T)
    proof (app {t₁ ∙ t₂} e₁∷T e₂∷T) with proof e₁∷T
    proof (app {t₁ ∙ t₂} {e₂} e₁∷T e₂∷T) | ⌜ n ⌝ , inj₁ t₁∙t₂⇒n = ⌜ n ⌝ ∙ e₂ , inj₁ (congruence1 t₁∙t₂⇒n)
    ... | ⌜ n ⌝ , inj₂ ()
    proof (app {t₁ ∙ t₂} {e₂} e₁∷T e₂∷T) | var x , inj₁ t₁∙t₂⇒x = var x ∙ e₂ , inj₁ (congruence1 t₁∙t₂⇒x)
    ... | var x , inj₂ ()
    proof (app {t₁ ∙ t₂} {e₂} e₁∷T e₂∷T) | t₁' ∙ t₂' , inj₁ t₁∙t₂⇒t₁'∙t₂' = (t₁' ∙ t₂') ∙ e₂ , inj₁ (congruence1 t₁∙t₂⇒t₁'∙t₂')
    ... | t₁' ∙ t₂' , inj₂ ()
    proof (app {t₁ ∙ t₂} {e₂} e₁∷T e₂∷T) | (Λ x ∷ T' , e₁') , inj₁ t₁∙t₂⇒Λ = (Λ x ∷ T' , e₁') ∙ e₂ , inj₁ (congruence1 t₁∙t₂⇒Λ)
    ... | (Λ x ∷ T' , e₁') , inj₂ ()
    proof (app {Λ x ∷ T , e₁} {e₂} e₁∷T e₂∷T) = e₁ [ x / e₂ ] , inj₁ contraction
