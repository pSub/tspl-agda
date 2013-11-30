open import Data.Nat
open import Data.Sum
open import Data.Product

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
  data Γ : Set where
    ∅ : Γ

  infixr 1 _⊢_∷_

  data _⊢_∷_ : Γ → E → T → Set where
    literal  : ∀ {n Γ} →  Γ ⊢ ⌜ n ⌝ ∷ Nat
    addition : ∀ {e₁ e₂ Γ} → Γ ⊢ e₁ ∷ Nat → Γ ⊢ e₂ ∷ Nat → Γ ⊢ e₁ ⊕ e₂ ∷ Nat

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

    proof : subjectexpansion
    proof (contraction n m) literal = addition literal literal
    proof (congruence1 e⇒e') (addition e₁∷Nat e₂∷Nat) = addition (proof e⇒e' e₁∷Nat) e₂∷Nat
    proof (congruence2 e⇒e') (addition e₁∷Nat e₂∷Nat) = addition e₁∷Nat (proof e⇒e' e₂∷Nat)

  module ProgressProof where
    open Progress language

    proof : progress
    proof (literal {n}) = ⌜ n ⌝ , (inj₂ num)
    proof (addition {⌜ n₁ ⌝} {⌜ n₂ ⌝} literal literal) = ⌜ n₁ + n₂ ⌝ , inj₁ (contraction n₁ n₂)
    proof (addition {⌜ n ⌝} {e₂ ⊕ e₂'} literal e₂∷T) with proof e₂∷T
    proof (addition {⌜ n ⌝} {e₂ ⊕ e₂'} literal e₂∷T) | ⌜ x ⌝ , inj₁ e₂⊕e₂'⇒⌜x⌝ = ⌜ n ⌝ ⊕ ⌜ x ⌝ , inj₁ (congruence2 e₂⊕e₂'⇒⌜x⌝)
    proof (addition {⌜ n ⌝} {e₂ ⊕ e₂'} literal e₂∷T) | ⌜ x ⌝ , inj₂ ()
    proof (addition {⌜ n ⌝} {e₂ ⊕ .e₂'} literal e₂∷T) | e₂* ⊕ e₂' , inj₁ (congruence1 e₂⇒e₂*) = ⌜ n ⌝ ⊕ (e₂* ⊕ e₂') , inj₁ (congruence2 (congruence1 e₂⇒e₂*))
    proof (addition {⌜ n ⌝} {.e₂ ⊕ e₂'} literal e₂∷T) | e₂ ⊕ e₂'* , inj₁ (congruence2 e₂'⇒e₂'*) = ⌜ n ⌝ ⊕ (e₂ ⊕ e₂'*) , inj₁ (congruence2 (congruence2 e₂'⇒e₂'*))
    proof (addition {⌜ n ⌝} {e₂ ⊕ e₂'} literal e₂∷T) | proj₁ ⊕ proj₂ , inj₂ ()
    proof (addition {e₁ ⊕ e₁'} {⌜ n ⌝} e₁∷T e₂∷T) with proof e₁∷T
    proof (addition {e₁ ⊕ e₁'} {⌜ n ⌝} e₁∷T e₂∷T) | ⌜ x ⌝ , inj₁ e₁⊕e₁'⇒⌜x⌝ = ⌜ x ⌝ ⊕ ⌜ n ⌝ , inj₁ (congruence1 e₁⊕e₁'⇒⌜x⌝)
    proof (addition {e₁ ⊕ e₁'} {⌜ n ⌝} e₁∷T e₂∷T) | ⌜ x ⌝ , inj₂ ()
    proof (addition {e₁ ⊕ .e₁'} {⌜ n ⌝} e₁∷T e₂∷T) | e₁* ⊕ e₁' , inj₁ (congruence1 e₁⇒e₁*) = (e₁* ⊕ e₁') ⊕ ⌜ n ⌝ , inj₁ (congruence1 (congruence1 e₁⇒e₁*))
    proof (addition {.e₁ ⊕ e₁'} {⌜ n ⌝} e₁∷T e₂∷T) | e₁ ⊕ e₁'* , inj₁ (congruence2 e₁'⇒e₁'*) = (e₁ ⊕ e₁'*) ⊕ ⌜ n ⌝ , inj₁ (congruence1 (congruence2 e₁'⇒e₁'*))
    proof (addition {e₁ ⊕ e₁'} {⌜ x ⌝} e₁∷T e₂∷T) | proj₁ ⊕ proj₂ , inj₂ ()
    proof (addition {e₁ ⊕ e₁'} {e₂ ⊕ e₃} e₁∷T e₂∷T) with proof e₁∷T
    proof (addition {e₁ ⊕ e₁'} {e₂ ⊕ e₃} e₁∷T e₂∷T) | ⌜ n ⌝ , inj₁ e₁⊕e₁'⇒⌜n⌝ = ⌜ n ⌝ ⊕ (e₂ ⊕ e₃) , inj₁ (congruence1 e₁⊕e₁'⇒⌜n⌝)
    proof (addition {e₁ ⊕ e₁'} {e₂ ⊕ e₃} e₁∷T e₂∷T) | ⌜ x ⌝ , inj₂ ()
    proof (addition {e₁ ⊕ .e₁'} {e₂ ⊕ e₃} e₁∷T e₂∷T) | e₁* ⊕ e₁' , inj₁ (congruence1 e₁⇒e₁*) = (e₁* ⊕ e₁') ⊕ (e₂ ⊕ e₃) , inj₁ (congruence1 (congruence1 e₁⇒e₁*))
    proof (addition {.e₁ ⊕ e₁'} {e₂ ⊕ e₃} e₁∷T e₂∷T) | e₁ ⊕ e₁'* , inj₁ (congruence2 e₁'⇒e₁'*) = ((e₁ ⊕ e₁'*) ⊕ (e₂ ⊕ e₃)) , (inj₁ (congruence1 (congruence2 e₁'⇒e₁'*)))
    proof (addition {e₁ ⊕ e₁'} {e₂ ⊕ e₃} e₁∷T e₂∷T) | proj₁ ⊕ proj₂ , inj₂ ()

  module PreservationProof where
    open Preservation language

    proof : preservation
    proof literal ()
    proof (addition e₁∷T e₂∷T) (contraction n m) = literal
    proof (addition e₁∷T e₂∷T) (congruence1 e₁⇒e₁') with proof e₁∷T e₁⇒e₁'
    ... | e₁'∷T = addition e₁'∷T e₂∷T
    proof (addition e₁∷T e₂∷T) (congruence2 e₂⇒e₂') with proof e₂∷T e₂⇒e₂'
    ... | e₂'∷T = addition e₁∷T e₂'∷T
