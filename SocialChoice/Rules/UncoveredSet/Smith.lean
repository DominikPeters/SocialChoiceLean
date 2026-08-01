import SocialChoice.Axioms.Smith
import SocialChoice.Rules.UncoveredSet.Defs
import SocialChoice.Rules.TopCycle.Defs

namespace SocialChoice

open Finset

lemma covers_of_dominatesSet {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) {S : Finset A} (hS : dominatesSet P S)
    {x y : A} (hy : y ∈ S) (hx : x ∉ S) :
    covers P y x := by
  classical
  have hyx : margin_pos P y x := hS.2 y hy x hx
  refine ⟨hyx, ?_, ?_⟩
  · intro z hxz
    by_cases hzS : z ∈ S
    · have hzx : margin_pos P z x := hS.2 z hzS x hx
      exact False.elim ((margin_pos_asymm (P := P) x z hxz) hzx)
    · exact hS.2 y hy z hzS
  · intro z hzy
    by_cases hzS : z ∈ S
    · exact hS.2 z hzS x hx
    · have hyz : margin_pos P y z := hS.2 y hy z hzS
      exact False.elim ((margin_pos_asymm (P := P) y z hyz) hzy)

lemma uncoveredSet_subset_of_dominatesSet {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) {S : Finset A} (hS : dominatesSet P S) :
    uncoveredSetOf (P := P) ⊆ S := by
  classical
  intro x hx
  by_contra hxS
  rcases hS.1 with ⟨y, hyS⟩
  have hcov : covers P y x := covers_of_dominatesSet (P := P) (S := S) hS hyS hxS
  have huncov : uncovered P x := (Finset.mem_filter.mp hx).2
  have hyx : y ≠ x := by
    intro hEq
    subst hEq
    exact hxS hyS
  exact (huncov y hyx) hcov

/-- uncoveredSet satisfies the Smith criterion. -/
theorem uncoveredSet_smithCriterion : SmithCriterion uncoveredSet := by
  intro V A _ _ P
  classical
  by_cases hA : Nonempty A
  · let _ : Nonempty A := hA
    have hsubset : uncoveredSetOf (P := P) ⊆ topCycleSet (P := P) :=
      uncoveredSet_subset_of_dominatesSet (P := P)
        (S := topCycleSet (P := P)) (topCycleSet_dominates (P := P))
    simpa [uncoveredSet, topCycle, hA] using hsubset
  · have hsubset : uncoveredSetOf (P := P) ⊆ (∅ : Finset A) := by
      intro x hx
      exact (False.elim (hA ⟨x⟩))
    simpa [uncoveredSet, topCycle, hA] using hsubset

end SocialChoice
