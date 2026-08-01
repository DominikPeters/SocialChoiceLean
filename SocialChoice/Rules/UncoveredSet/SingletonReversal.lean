import SocialChoice.Axioms.Implications
import SocialChoice.Axioms.Reversal
import SocialChoice.Rules.UncoveredSet.Defs
import SocialChoice.Rules.UncoveredSet.Smith

namespace SocialChoice

lemma uncoveredSet_singleton_implies_condorcetWinner {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (x : A) (hset : uncoveredSet P = ({x} : Finset A)) :
    CondorcetWinner P x := by
  rw [CondorcetWinner_iff_margin_pos]
  intro y hxy
  have hy_not_mem : y ∉ uncoveredSet P := by
    intro hy_mem
    have hy_single : y ∈ ({x} : Finset A) := by
      simpa [hset] using hy_mem
    have hy_eq : y = x := by
      simpa using (Finset.mem_singleton.mp hy_single)
    exact hxy hy_eq.symm
  have hy_not_uncovered : ¬ uncovered P y := by
    intro hy_uncov
    exact hy_not_mem (by simpa [uncoveredSet, uncoveredSetOf] using hy_uncov)
  let _ : Preorder A := {
    le := fun a b => a = b ∨ covers P b a
    le_refl := by
      intro a
      exact Or.inl rfl
    le_trans := by
      intro a b c hab hbc
      cases hab with
      | inl hab =>
          subst hab
          exact hbc
      | inr hab =>
          cases hbc with
          | inl hbc =>
              subst hbc
              exact Or.inr hab
          | inr hbc =>
              exact Or.inr (covers_trans (P := P) hbc hab)
  }
  obtain ⟨z, hyz, hzmax⟩ :=
    Finite.exists_le_maximal (a := y) (p := fun _ : A => True) trivial
  have hz_uncov : uncovered P z := by
    intro w hwz hwcov
    have hzw : z ≤ w := Or.inr hwcov
    have hwz' : w ≤ z := hzmax.2 trivial hzw
    cases hwz' with
    | inl hwz' =>
        exact (hwz hwz').elim
    | inr hwz' =>
        exact (covers_asymm (P := P) hwz') hwcov
  have hz_mem : z ∈ uncoveredSet P := by
    simpa [uncoveredSet, uncoveredSetOf] using hz_uncov
  have hzx : z = x := by
    simpa [hset] using hz_mem
  have hyx' : y ≤ x := by
    simpa [hzx] using hyz
  have hcovers : covers P x y := by
    cases hyx' with
    | inl hyx' =>
        exact (hxy hyx'.symm).elim
    | inr hyx' =>
        exact hyx'
  exact hcovers.1

theorem uncoveredSet_singleton_reversal_symmetry : SingletonReversalSymmetry uncoveredSet := by
  intro V A _ _ P x hnontriv hsingleton
  have hnontriv' : ∃ d, d ≠ x := by
    rcases hnontriv with ⟨d, hd⟩
    exact ⟨d, fun hdx => hd hdx.symm⟩
  have hcw : CondorcetWinner P x :=
    uncoveredSet_singleton_implies_condorcetWinner (P := P) (x := x) hsingleton
  have hloser_rev : CondorcetLoser (reverse_profile P) x := by
    refine (CondorcetLoser_iff_margin_pos (P := reverse_profile P) (c := x)).2 ?_
    refine ⟨?_, hnontriv'⟩
    intro y hxy
    have hpos : margin_pos P x y :=
      (CondorcetWinner_iff_margin_pos (P := P) (c := x)).1 hcw y hxy
    simpa [margin_pos, margin_reverse_eq] using hpos
  have hloserCrit : CondorcetLoserCriterion uncoveredSet := by
    apply Implies.apply smithCriterion_implies_condorcetLoserCriterion_Imp (f := uncoveredSet)
    · exact uncoveredSet_isVotingRule
    · exact uncoveredSet_smithCriterion
  exact hloserCrit (P := reverse_profile P) (c := x) hloser_rev

end SocialChoice
