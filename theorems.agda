open import language

module theorems where

module SubjectExpansion (l : TypedLanguage) where
       open TypedLanguage l

       subjectexpansion : Set
       subjectexpansion = ∀ {e e' Γ T} → e ⇒ e' → Γ ⊢ e' ∷ T → Γ ⊢ e ∷ T

module EraseEvaluation (l : TypedLanguage)
                       (l' : UntypedLanguage)
                       (erase : TypedLanguage.E l → UntypedLanguage.E l') where

        _⇒ₜ_ = TypedLanguage._⇒_ l
        _⇒ᵤ_ = UntypedLanguage._⇒_ l'

        eraseEvalutation : Set
        eraseEvalutation = ∀ {e₁ e₂} → e₁ ⇒ₜ e₂ → erase e₁ ⇒ᵤ erase e₂
