import Mathlib.Tactic
import SocialChoice.Margin
import SocialChoice.Axioms.Reversal
import SocialChoice.Rules.Black.Defs
import SocialChoice.Rules.Black.Condorcet
import SocialChoice.Rules.Black.CondorcetLoser
import SocialChoice.Rules.ScoringRules.Borda.Reversal

namespace SocialChoice

open Finset
open Classical

private lemma exists_ne_of_black_ne_univ {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (x : A) (hnot : black P ≠ (Finset.univ : Finset A)) :
    ∃ y, y ≠ x := by
  classical
  by_contra h
  push Not at h
  have hnonempty : (black P).Nonempty := by
    let _ : Nonempty A := ⟨x⟩
    exact black_isVotingRule (P := P)
  rcases hnonempty with ⟨y, hy⟩
  have hyx : y = x := h y
  have hxmem : x ∈ black P := by
    simpa [hyx] using hy
  have hsubset : (Finset.univ : Finset A) ⊆ black P := by
    intro z _hz
    have hzx : z = x := h z
    subst hzx
    exact hxmem
  have hblack_univ : black P = (Finset.univ : Finset A) := by
    apply Finset.ext
    intro z
    constructor
    · intro _hz
      exact Finset.mem_univ z
    · intro hz
      exact hsubset hz
  exact hnot hblack_univ

private lemma condorcetWinner_to_condorcetLoser_reverse {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) {x : A} (hwin : CondorcetWinner P x) (hne : ∃ y, y ≠ x) :
    CondorcetLoser (reverse_profile P) x := by
  have hpos : ∀ d, x ≠ d → margin_pos P x d :=
    (CondorcetWinner_iff_margin_pos P x).1 hwin
  refine (CondorcetLoser_iff_margin_pos (P := reverse_profile P) (c := x)).2 ?_
  refine ⟨?_, hne⟩
  intro d hdx
  have hpos' : margin_pos P x d := hpos d hdx
  simpa [margin_pos, margin_reverse_eq] using hpos'

private lemma condorcetWinner_reverse_to_condorcetLoser {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) {x : A} (hwin : CondorcetWinner (reverse_profile P) x)
    (hne : ∃ y, y ≠ x) : CondorcetLoser P x := by
  have hpos : ∀ d, x ≠ d → margin_pos (reverse_profile P) x d :=
    (CondorcetWinner_iff_margin_pos (reverse_profile P) x).1 hwin
  refine (CondorcetLoser_iff_margin_pos (P := P) (c := x)).2 ?_
  refine ⟨?_, hne⟩
  intro d hdx
  have hpos' : margin_pos (reverse_profile P) x d := hpos d hdx
  simpa [margin_pos, margin_reverse_eq] using hpos'

theorem black_reversal_symmetry : ReversalSymmetry black := by
  intro V A _ _ _ P hnot
  classical
  by_cases hcw : ∃ x, CondorcetWinner P x
  · let x := Classical.choose hcw
    have hxwin : CondorcetWinner P x := Classical.choose_spec hcw
    have hblackP : black P = ({x} : Finset A) := by
      simp [black, hcw, x]
    have hne : ∃ y, y ≠ x := exists_ne_of_black_ne_univ (P := P) x hnot
    have hloser_rev : CondorcetLoser (reverse_profile P) x :=
      condorcetWinner_to_condorcetLoser_reverse (P := P) (x := x) hxwin hne
    have hxnot : x ∉ black (reverse_profile P) :=
      black_CondorcetLoser_criterion (P := reverse_profile P) (c := x) hloser_rev
    apply Finset.ext
    intro y
    constructor
    · intro hy
      rcases Finset.mem_inter.mp hy with ⟨hyP, hyR⟩
      have hyx : y = x := by
        have : y ∈ ({x} : Finset A) := by
          simpa [hblackP] using hyP
        simpa using this
      subst hyx
      exact (hxnot hyR).elim
    · intro hy
      cases hy
  · have hblackP : black P = borda P := by
      simp [black, hcw]
    by_cases hcw_rev : ∃ x, CondorcetWinner (reverse_profile P) x
    · let x := Classical.choose hcw_rev
      have hxwin : CondorcetWinner (reverse_profile P) x := Classical.choose_spec hcw_rev
      have hblackRev : black (reverse_profile P) = ({x} : Finset A) := by
        simp [black, hcw_rev, x]
      have hne : ∃ y, y ≠ x := exists_ne_of_black_ne_univ (P := P) x hnot
      have hloser : CondorcetLoser P x :=
        condorcetWinner_reverse_to_condorcetLoser (P := P) (x := x) hxwin hne
      have hxnot : x ∉ black P :=
        black_CondorcetLoser_criterion (P := P) (c := x) hloser
      apply Finset.ext
      intro y
      constructor
      · intro hy
        rcases Finset.mem_inter.mp hy with ⟨hyP, hyR⟩
        have hyx : y = x := by
          have : y ∈ ({x} : Finset A) := by
            simpa [hblackRev] using hyR
          simpa using this
        subst hyx
        exact (hxnot hyP).elim
      · intro hy
        cases hy
    · have hblackRev : black (reverse_profile P) = borda (reverse_profile P) := by
        simp [black, hcw_rev]
      have hnot_borda : borda P ≠ (Finset.univ : Finset A) := by
        simpa [hblackP] using hnot
      have hsym : borda P ∩ borda (reverse_profile P) = ∅ :=
        borda_reversal_symmetry (P := P) hnot_borda
      simpa [hblackP, hblackRev] using hsym

end SocialChoice
