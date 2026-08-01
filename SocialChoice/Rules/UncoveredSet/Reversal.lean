import SocialChoice.Axioms.Reversal
import SocialChoice.Margin
import SocialChoice.Rules.UncoveredSet.Defs
import SocialChoice.Rules.SplitCycle.Reversal
import Mathlib.Tactic.FinCases

namespace SocialChoice

open Finset

section ReversalCounterexample

lemma reversalCounterexample_margin_pos_12 :
    margin_pos reversalCounterexampleProfile (1 : Fin 3) (2 : Fin 3) := by
  have hiff :
      margin_pos reversalCounterexampleProfile (1 : Fin 3) (2 : Fin 3) ↔
        marginList (fun v => (reversalCounterexampleBallots v).ranking) 1 2 > 0 := by
    simpa [reversalCounterexampleProfile] using
      (margin_pos_iff_marginList_pos (ballots := reversalCounterexampleBallots)
        (a := (1 : Fin 3)) (b := (2 : Fin 3)))
  have hpos :
      marginList (fun v => (reversalCounterexampleBallots v).ranking) 1 2 > 0 := by
    simp [reversalCounterexample_marginList_12]
  exact hiff.mpr hpos

lemma reversalCounterexample_no_margin_pos_to_0 (y : Fin 3) :
    ¬ margin_pos reversalCounterexampleProfile y (0 : Fin 3) := by
  fin_cases y <;>
    simp [reversalCounterexampleProfile, margin_pos_iff_marginList_pos,
      reversalCounterexample_marginList_00,
      reversalCounterexample_marginList_10,
      reversalCounterexample_marginList_20]

lemma reversalCounterexample_no_margin_pos_from_0 (y : Fin 3) :
    ¬ margin_pos reversalCounterexampleProfile (0 : Fin 3) y := by
  fin_cases y <;>
    simp [reversalCounterexampleProfile, margin_pos_iff_marginList_pos,
      reversalCounterexample_marginList_00,
      reversalCounterexample_marginList_01,
      reversalCounterexample_marginList_02]

lemma reversalCounterexample_no_margin_pos_from_2 (y : Fin 3) :
    ¬ margin_pos reversalCounterexampleProfile (2 : Fin 3) y := by
  fin_cases y <;>
    simp [reversalCounterexampleProfile, margin_pos_iff_marginList_pos,
      reversalCounterexample_marginList_20,
      reversalCounterexample_marginList_21,
      reversalCounterexample_marginList_22]

lemma reversalCounterexample_no_margin_pos_to_1 (y : Fin 3) :
    ¬ margin_pos reversalCounterexampleProfile y (1 : Fin 3) := by
  fin_cases y <;>
    simp [reversalCounterexampleProfile, margin_pos_iff_marginList_pos,
      reversalCounterexample_marginList_01,
      reversalCounterexample_marginList_11,
      reversalCounterexample_marginList_21]

lemma reversalCounterexample_covers_12 :
    covers reversalCounterexampleProfile (1 : Fin 3) (2 : Fin 3) := by
  refine ⟨reversalCounterexample_margin_pos_12, ?_, ?_⟩
  · intro z hz
    exact (False.elim ((reversalCounterexample_no_margin_pos_from_2 z) hz))
  · intro z hz
    exact (False.elim ((reversalCounterexample_no_margin_pos_to_1 z) hz))

lemma reversalCounterexample_zero_uncovered :
    uncovered reversalCounterexampleProfile (0 : Fin 3) := by
  intro y _hy hcov
  exact (reversalCounterexample_no_margin_pos_to_0 y) hcov.1

lemma reversalCounterexample_zero_mem_uncoveredSet :
    (0 : Fin 3) ∈ uncoveredSet reversalCounterexampleProfile := by
  classical
  simp [uncoveredSet, uncoveredSetOf, reversalCounterexample_zero_uncovered]

lemma reversalCounterexample_zero_mem_uncoveredSet_reverse :
    (0 : Fin 3) ∈ uncoveredSet (reverse_profile reversalCounterexampleProfile) := by
  classical
  simp [uncoveredSet, uncoveredSetOf]
  intro y _hy hcov
  have hpos : margin_pos reversalCounterexampleProfile (0 : Fin 3) y := by
    simpa [margin_pos, margin_reverse_eq] using hcov.1
  exact (reversalCounterexample_no_margin_pos_from_0 y) hpos

lemma reversalCounterexample_two_not_mem_uncoveredSet :
    (2 : Fin 3) ∉ uncoveredSet reversalCounterexampleProfile := by
  classical
  have hcover : covers reversalCounterexampleProfile (1 : Fin 3) (2 : Fin 3) :=
    reversalCounterexample_covers_12
  have hnot : ¬ uncovered reversalCounterexampleProfile (2 : Fin 3) := by
    intro huncov
    exact (huncov (1 : Fin 3) (by decide)) hcover
  simpa [uncoveredSet, uncoveredSetOf] using hnot

lemma reversalCounterexample_uncoveredSet_ne_univ :
    uncoveredSet reversalCounterexampleProfile ≠ Finset.univ := by
  intro hEq
  have hmem : (2 : Fin 3) ∈ uncoveredSet reversalCounterexampleProfile := by
    simp [hEq]
  exact reversalCounterexample_two_not_mem_uncoveredSet hmem

theorem uncoveredSet_not_reversal_symmetry : ¬ ReversalSymmetry uncoveredSet := by
  intro h
  have hne : uncoveredSet reversalCounterexampleProfile ≠ Finset.univ :=
    reversalCounterexample_uncoveredSet_ne_univ
  have hEq := h (P := reversalCounterexampleProfile) hne
  have hmem : (0 : Fin 3) ∈
      uncoveredSet reversalCounterexampleProfile ∩
        uncoveredSet (reverse_profile reversalCounterexampleProfile) := by
    exact Finset.mem_inter.mpr
      ⟨reversalCounterexample_zero_mem_uncoveredSet,
       reversalCounterexample_zero_mem_uncoveredSet_reverse⟩
  have hmem' := hmem
  simp [hEq] at hmem'

end ReversalCounterexample

end SocialChoice
