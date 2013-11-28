open import language

module theorems where

module SubjectExpansion (l : TypedLanguage) where
       open TypedLanguage l

       subjectexpansion : Set
       subjectexpansion = ∀ {e e' Γ T} → e ⇒ e' → Γ ⊢ e' ∷ T → Γ ⊢ e ∷ T
