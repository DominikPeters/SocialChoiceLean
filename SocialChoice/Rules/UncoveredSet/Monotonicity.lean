import SocialChoice.Axioms.Monotonicity
import SocialChoice.Rules.UncoveredSet.Defs

namespace SocialChoice

open Finset

lemma covers_of_simpleLift {V A : Type} [Fintype V] [Fintype A]
    {P P' : Profile V A} {x y : A} (hLift : simpleLift P' P x) :
    covers P' y x → covers P y x := by
  intro hcov'
  rcases hcov' with ⟨hpos', h2', h3'⟩
  have hyx : y ≠ x := ne_of_margin_pos (P := P') hpos'
  have hle : margin P' y x ≤ margin P y x :=
    margin_le_of_simpleLift_ax (P := P) (P' := P') (x := x) (a := y) hLift
  have hpos : margin_pos P y x := by
    have hpos'': 0 < margin P' y x := by
      simpa [margin_pos] using hpos'
    have hpos''': 0 < margin P y x := lt_of_lt_of_le hpos'' hle
    simpa [margin_pos] using hpos'''
  refine ⟨hpos, ?_, ?_⟩
  · intro z hz
    have hz' : margin_pos P' x z := by
      have hle2 : margin P x z ≤ margin P' x z :=
        margin_le_of_simpleLift_xa (P := P) (P' := P') (x := x) (a := z) hLift
      have hz0 : 0 < margin P x z := by
        simpa [margin_pos] using hz
      have hz0' : 0 < margin P' x z := lt_of_lt_of_le hz0 hle2
      simpa [margin_pos] using hz0'
    have hyz' : margin_pos P' y z := h2' z hz'
    by_cases hzx : z = x
    · subst hzx
      simpa using hpos
    · have hEq : margin P y z = margin P' y z :=
        margin_eq_of_simpleLift P P' x y z hyx hzx hLift
      simpa [margin_pos, hEq] using hyz'
  · intro z hz
    have hzy' : margin_pos P' z y := by
      by_cases hzx : z = x
      · subst hzx
        have hxny : ¬ margin_pos P z y := (margin_pos_asymm (P := P) y z hpos)
        exact (hxny hz).elim
      · have hEq : margin P z y = margin P' z y :=
          margin_eq_of_simpleLift P P' x z y hzx hyx hLift
        simpa [margin_pos, hEq] using hz
    have hzx' : margin_pos P' z x := h3' z hzy'
    have hle3 : margin P' z x ≤ margin P z x :=
      margin_le_of_simpleLift_ax (P := P) (P' := P') (x := x) (a := z) hLift
    have hzx0 : 0 < margin P' z x := by
      simpa [margin_pos] using hzx'
    have hzx0' : 0 < margin P z x := lt_of_lt_of_le hzx0 hle3
    simpa [margin_pos] using hzx0'

/-- uncoveredSet satisfies monotonicity under simple lifts. -/
theorem uncoveredSet_monotonicity : Monotonicity uncoveredSet := by
  intro V A _ _ P P' x hx hLift
  classical
  have hx' : x ∈ uncoveredSetOf (P := P) := by
    simpa [uncoveredSet] using hx
  have hx_uncov : uncovered P x := (Finset.mem_filter.mp hx').2
  have hx_uncov' : uncovered P' x := by
    intro y hyx hcov'
    have hcov : covers P y x := covers_of_simpleLift (P := P) (P' := P') (x := x) (y := y) hLift hcov'
    exact hx_uncov y hyx hcov
  have hx'' : x ∈ uncoveredSetOf (P := P') :=
    Finset.mem_filter.mpr ⟨by simp, hx_uncov'⟩
  simpa [uncoveredSet] using hx''

end SocialChoice
