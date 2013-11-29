open import language
open import Data.Product
open import Data.Sum

module theorems where

module Progress (l : TypedLanguage) where
       open TypedLanguage l

       progress : Set
       progress = ∀ {e Γ T} → Γ ⊢ e ∷ T → ∃ \e' → (e ⇒ e') ⊎ Val e

module Preservation (l : TypedLanguage) where
       open TypedLanguage l

       preservation : Set
       preservation = ∀ {e e' Γ T} → Γ ⊢ e ∷ T → e ⇒ e' → Γ ⊢ e' ∷ T

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
