import Mathlib.Data.Finset.Basic
import Mathlib.Order.Preorder.Finite
import SocialChoice.Profile
import SocialChoice.Margin
import SocialChoice.Meta

namespace SocialChoice

open Finset

/--
`x` covers `y` if `x` strictly majority-dominates `y`, every alternative strictly
majority-dominated by `y` is strictly majority-dominated by `x`, and every
alternative that strictly majority-dominates `x` also strictly
majority-dominates `y`.

This is **McKelvey covering** (left- and right-covering combined). All common
covering variants (Fishburn, Gillies, McKelvey) coincide on tournaments, i.e.
when there are no pairwise majority ties, but they differ in the presence of
ties; theorems about `uncoveredSet` are claims about the McKelvey variant.
-/
def covers {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (x y : A) : Prop :=
  margin_pos P x y ∧
  (∀ z, margin_pos P y z → margin_pos P x z) ∧
  (∀ z, margin_pos P z x → margin_pos P z y)

lemma covers_trans {V A : Type} [Fintype V] [Fintype A]
    {P : Profile V A} {x y z : A}
    (hxy : covers P x y) (hyz : covers P y z) :
    covers P x z := by
  rcases hxy with ⟨hxy1, hxy2, hxy3⟩
  rcases hyz with ⟨hyz1, hyz2, hyz3⟩
  refine ⟨?_, ?_, ?_⟩
  · exact hxy2 z hyz1
  · intro w hzw
    exact hxy2 w (hyz2 w hzw)
  · intro w hwx
    exact hyz3 w (hxy3 w hwx)

lemma covers_asymm {V A : Type} [Fintype V] [Fintype A]
    {P : Profile V A} {x y : A} (hxy : covers P x y) :
    ¬ covers P y x := by
  intro hyx
  exact (margin_pos_asymm (P := P) x y hxy.1) hyx.1

/-- An alternative is uncovered if no distinct alternative covers it. -/
def uncovered {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (x : A) : Prop :=
  ∀ y, y ≠ x → ¬ covers P y x

/-- The uncovered set of a profile. -/
noncomputable def uncoveredSetOf {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) : Finset A := by
  classical
  exact Finset.univ.filter (fun x => uncovered P x)

lemma uncoveredSet_nonempty {V A : Type} [Fintype V] [Fintype A] [Nonempty A]
    (P : Profile V A) : (uncoveredSetOf (P := P)).Nonempty := by
  classical
  let _ : LE A := ⟨fun x y => x = y ∨ covers P y x⟩
  have _ : IsTrans A (· ≤ ·) := by
    refine ⟨?_⟩
    intro x y z hxy hyz
    cases hxy with
    | inl hxy =>
        subst hxy
        exact hyz
    | inr hxy =>
        cases hyz with
        | inl hyz =>
            subst hyz
            exact Or.inr hxy
        | inr hyz =>
            exact Or.inr (covers_trans (P := P) hyz hxy)
  have hne : (Finset.univ : Finset A).Nonempty := Finset.univ_nonempty
  obtain ⟨x, hxmax⟩ :=
    (Finset.univ : Finset A).exists_maximalFor (f := id) hne
  have hxuncov : uncovered P x := by
    intro y hyx hcov
    have hxy : x ≤ y := Or.inr hcov
    have hyx' : y ≤ x := hxmax.2 (by simp) hxy
    cases hyx' with
    | inl hEq => exact (hyx hEq).elim
    | inr hcov' => exact (covers_asymm (P := P) hcov') hcov
  refine ⟨x, ?_⟩
  exact Finset.mem_filter.mpr ⟨by simp, hxuncov⟩

@[scRule]
noncomputable def uncoveredSet : VotingRule := by
  intro V A _ _ P
  classical
  exact uncoveredSetOf (P := P)

theorem uncoveredSet_isVotingRule : IsVotingRule uncoveredSet := by
  intro V A _ _ _ P
  classical
  have hA : Nonempty A := inferInstance
  have hne : (uncoveredSetOf (P := P)).Nonempty :=
    uncoveredSet_nonempty (P := P)
  simpa [uncoveredSet] using hne

end SocialChoice
