import Mathlib.Tactic
import SocialChoice.Axioms.Reversal
import SocialChoice.Rules.ScoringRules.Borda.C2Borda

namespace SocialChoice

open Finset
open Classical

lemma c2BordaRule_score_pos_of_exists_pos {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) {x : A} (hx : x ∈ c2BordaRule P)
    (hpos : ∃ y, 0 < c2BordaScore P y) :
    0 < c2BordaScore P x := by
  classical
  by_cases hA : (Finset.univ : Finset A).Nonempty
  · let scoreSet : Finset Int :=
      (Finset.univ.image (fun c => c2BordaScore P c))
    let maxScore : Int :=
      scoreSet.max' (by
        simpa [scoreSet, Finset.Nonempty] using
          (hA.image (fun c => c2BordaScore P c)))
    have hx' : c2BordaScore P x = maxScore := by
      simpa [c2BordaRule, hA, scoreSet, maxScore] using hx
    rcases hpos with ⟨y, hy⟩
    have hy_mem : c2BordaScore P y ∈ scoreSet := by
      exact Finset.mem_image.mpr ⟨y, by simp, rfl⟩
    have hle : c2BordaScore P y ≤ maxScore :=
      Finset.le_max' scoreSet _ hy_mem
    have hpos_max : 0 < maxScore := lt_of_lt_of_le hy hle
    simpa [hx'] using hpos_max
  · have : False := by
      simp [c2BordaRule, hA] at hx
    exact this.elim

theorem borda_reversal_symmetry : ReversalSymmetry borda := by
  intro V A _ _ _ P hnot
  classical
  by_cases hA : (Finset.univ : Finset A).Nonempty
  · have hborda : borda P = c2BordaRule P :=
      borda_eq_c2BordaRule (P := P)
    have hborda_rev : borda (reverse_profile P) = c2BordaRule (reverse_profile P) :=
      borda_eq_c2BordaRule (P := reverse_profile P)
    have hnot' : c2BordaRule P ≠ Finset.univ := by
      simpa [hborda] using hnot
    have hnonzero : ∃ x, c2BordaScore P x ≠ 0 := by
      by_contra hall
      have hall' : ∀ x, c2BordaScore P x = 0 := by
        push Not at hall
        exact hall
      have : c2BordaRule P = Finset.univ :=
        c2BordaRule_eq_univ_of_all_zero (P := P) hall'
      exact hnot' this
    obtain ⟨hpos_ex, hneg_ex⟩ :
        (∃ x, 0 < c2BordaScore P x) ∧ (∃ x, c2BordaScore P x < 0) := by
      rcases hnonzero with ⟨x, hxne⟩
      have hlt_or_gt : c2BordaScore P x < 0 ∨ 0 < c2BordaScore P x := by
        exact lt_or_gt_of_ne hxne
      cases hlt_or_gt with
      | inl hneg =>
          have hpos_ex : ∃ y, 0 < c2BordaScore P y :=
            exists_pos_c2BordaScore_of_neg (P := P) (c := x) hneg
          exact ⟨hpos_ex, ⟨x, hneg⟩⟩
      | inr hpos =>
          have hneg_ex : ∃ y, c2BordaScore P y < 0 :=
            exists_neg_c2BordaScore_of_pos (P := P) (c := x) hpos
          exact ⟨⟨x, hpos⟩, hneg_ex⟩
    have hpos_rev : ∃ y, 0 < c2BordaScore (reverse_profile P) y := by
      rcases hneg_ex with ⟨y, hyneg⟩
      refine ⟨y, ?_⟩
      have : 0 < - c2BordaScore P y := by
        linarith
      simpa [c2BordaScore_reverse (P := P) (x := y)] using this
    ext x
    constructor
    · intro hx
      rcases Finset.mem_inter.mp hx with ⟨hxP, hxR⟩
      have hxP' : x ∈ c2BordaRule P := by
        simpa [hborda] using hxP
      have hxR' : x ∈ c2BordaRule (reverse_profile P) := by
        simpa [hborda_rev] using hxR
      have hxpos : 0 < c2BordaScore P x :=
        c2BordaRule_score_pos_of_exists_pos (P := P) hxP' hpos_ex
      have hxpos_rev : 0 < c2BordaScore (reverse_profile P) x :=
        c2BordaRule_score_pos_of_exists_pos (P := reverse_profile P) hxR' hpos_rev
      have hxneg : c2BordaScore P x < 0 := by
        have : 0 < - c2BordaScore P x := by
          simpa [c2BordaScore_reverse (P := P) (x := x)] using hxpos_rev
        linarith
      have : False := lt_asymm hxpos hxneg
      exact this.elim
    · intro hx
      cases hx
  · have hborda : borda P = ∅ := by
      simp [borda, scoringRule, scoringWinners, hA]
    have hborda_rev : borda (reverse_profile P) = ∅ := by
      simp [borda, scoringRule, scoringWinners, hA]
    simp [hborda, hborda_rev]

end SocialChoice
