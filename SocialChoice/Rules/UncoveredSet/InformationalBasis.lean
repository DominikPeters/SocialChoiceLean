import SocialChoice.Axioms.InformationalBasis
import SocialChoice.Rules.UncoveredSet.Defs

namespace SocialChoice

lemma covers_eq_of_margins {V₁ V₂ A : Type} [Fintype V₁] [Fintype V₂] [Fintype A]
    (P₁ : Profile V₁ A) (P₂ : Profile V₂ A)
    (hmargin : ∀ x y : A, margin P₁ x y = margin P₂ x y) (x y : A) :
    covers P₁ x y ↔ covers P₂ x y := by
  classical
  simp [covers, margin_pos, hmargin]

lemma uncovered_eq_of_margins {V₁ V₂ A : Type} [Fintype V₁] [Fintype V₂] [Fintype A]
    (P₁ : Profile V₁ A) (P₂ : Profile V₂ A)
    (hmargin : ∀ x y : A, margin P₁ x y = margin P₂ x y) (x : A) :
    uncovered P₁ x ↔ uncovered P₂ x := by
  classical
  simp [uncovered, covers, margin_pos, hmargin]

lemma uncoveredSet_eq_of_margins {V₁ V₂ A : Type} [Fintype V₁] [Fintype V₂] [Fintype A]
    (P₁ : Profile V₁ A) (P₂ : Profile V₂ A)
    (hmargin : ∀ x y : A, margin P₁ x y = margin P₂ x y) :
    uncoveredSetOf (P := P₁) = uncoveredSetOf (P := P₂) := by
  classical
  ext x
  simp [uncoveredSetOf, uncovered, covers, margin_pos, hmargin]

/-- uncoveredSet depends only on margins. -/
theorem uncoveredSet_marginBased : MarginBased uncoveredSet := by
  intro V₁ V₂ A _ _ _ P₁ P₂ hmargin
  classical
  have hset : uncoveredSetOf (P := P₁) = uncoveredSetOf (P := P₂) :=
    uncoveredSet_eq_of_margins (P₁ := P₁) (P₂ := P₂) hmargin
  simp [uncoveredSet, hset]

end SocialChoice
