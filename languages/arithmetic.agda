open import Data.Nat
open import language
open import theorems

module languages.arithmetic where
  data E : Set where
    ⌜_⌝ : ℕ → E
    _⊕_ : E → E → E

  data Val : E → Set where
    num : ∀ {n} → Val ⌜ n ⌝

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

  arithmetic : TypedLanguage
  arithmetic = record
               { E = E
               ; Val = Val
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
