open import language

module theorems where

module SubjectExpansion (l : Language) where
       open Language l

       subjectexpansion : Set
       subjectexpansion = ∀ {e e' Γ T} → e ⇒ e' → Γ ⊢ e' ∷ T → Γ ⊢ e ∷ T
