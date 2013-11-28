open import Data.Bool
open import Data.Char
open import Relation.Binary.Core
open import Relation.Binary.PropositionalEquality

open import theorems
open import helper

module interlanguage where

  module EraseEvalLambdaCalculus where
    import languages.untypedLambdaCalculus as untyped
    import languages.typedLambdaCalculus as typed

    erase : typed.E → untyped.E
    erase (typed.num n) = untyped.num n
    erase (typed.var x) = untyped.var x
    erase (e₁ typed.∙ e₂) = (erase e₁) untyped.∙ (erase e₂)
    erase (typed.Λ x ∷ T , e) = untyped.Λ x , (erase e)

    open EraseEvaluation typed.language
                         untyped.language
                         erase

    -- TODO Would be nice to proof this, but the types get really ugly.
    postulate FV≡ : ∀ e y → y ∈? (typed.FV e) ≡ y ∈? (untyped.FV (erase e))
    
    lemma : ∀ x e₁ e₂ → erase (e₁ typed.[ x / e₂ ]) ≡ (erase e₁) untyped.[ x / (erase e₂) ]
    lemma x (typed.num n) e₂ = refl
    lemma x (typed.var y) e₂ with y == x
    ... | true = refl
    ... | false = refl
    lemma x (e₁ typed.∙ e₂) e₃ with lemma x e₁ e₃ | lemma x e₂ e₃
    ... | ih₁ | ih₂ = cong₂ untyped._∙_ ih₁ ih₂
    lemma x (typed.Λ y ∷ T , e₁) e₂ with x /= y | not (y ∈? (typed.FV e₂)) | not (y ∈? (untyped.FV (erase e₂))) | cong not (FV≡ e₂ y)
    ... | true | true | true | z = cong (untyped.Λ_,_ y) (lemma x e₁ e₂)
    ... | true | true | false | ()
    ... | true | false | true | ()
    ... | true | false | false | z = cong (untyped.Λ_,_ y) refl
    ... | false | _ | _ | z = refl

    proof : eraseEvalutation
    proof (typed.contraction {e₁} {e₂} {x}) with lemma x e₁ e₂ | untyped.contraction {erase e₁} {erase e₂} {x}
    ... | erase-dist | step = subst (untyped._⇒_ ((untyped.Λ x , erase e₁) untyped.∙ erase e₂)) (sym erase-dist) step
    proof (typed.congruence1 e₁⇒ₜe₁') = untyped.congruence1 (proof e₁⇒ₜe₁')
    proof (typed.congruence2 e₂⇒ₜe₂') = untyped.congruence2 (proof e₂⇒ₜe₂')
