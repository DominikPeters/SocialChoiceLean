import Mathlib.Tactic
import Mathlib.Tactic.FinCases
import SocialChoice.Axioms.Reversal
import SocialChoice.ListBallot
import SocialChoice.Rules.Minimax.Defs

namespace SocialChoice

open Finset

namespace MinimaxReversalCounterexample

def ballot2103 : ListBallot 4 := ListBallot.mk' [2, 1, 0, 3]
def ballot3021 : ListBallot 4 := ListBallot.mk' [3, 0, 2, 1]
def ballot3102 : ListBallot 4 := ListBallot.mk' [3, 1, 0, 2]

def ballots : Fin 3 → ListBallot 4
  | 0 => ballot2103
  | 1 => ballot3021
  | 2 => ballot3102

noncomputable def profile : Profile (Fin 3) (Fin 4) :=
  profileOfListBallots ballots

private lemma margin_profile_0_1 : margin profile (0 : Fin 4) (1 : Fin 4) = -1 := by
  rw [profile, margin_profileOfListBallots]
  decide

private lemma margin_profile_0_2 : margin profile (0 : Fin 4) (2 : Fin 4) = 1 := by
  rw [profile, margin_profileOfListBallots]
  decide

private lemma margin_profile_0_3 : margin profile (0 : Fin 4) (3 : Fin 4) = -1 := by
  rw [profile, margin_profileOfListBallots]
  decide

private lemma margin_profile_1_2 : margin profile (1 : Fin 4) (2 : Fin 4) = -1 := by
  rw [profile, margin_profileOfListBallots]
  decide

private lemma margin_profile_1_3 : margin profile (1 : Fin 4) (3 : Fin 4) = -1 := by
  rw [profile, margin_profileOfListBallots]
  decide

private lemma margin_profile_2_3 : margin profile (2 : Fin 4) (3 : Fin 4) = -1 := by
  rw [profile, margin_profileOfListBallots]
  decide

private lemma margin_profile_1_0 : margin profile (1 : Fin 4) (0 : Fin 4) = 1 := by
  have h := margin_antisymmetric (P := profile) (a := (1 : Fin 4)) (b := (0 : Fin 4))
  simpa [margin_profile_0_1] using h

private lemma margin_profile_2_0 : margin profile (2 : Fin 4) (0 : Fin 4) = -1 := by
  have h := margin_antisymmetric (P := profile) (a := (2 : Fin 4)) (b := (0 : Fin 4))
  simpa [margin_profile_0_2] using h

private lemma margin_profile_3_0 : margin profile (3 : Fin 4) (0 : Fin 4) = 1 := by
  have h := margin_antisymmetric (P := profile) (a := (3 : Fin 4)) (b := (0 : Fin 4))
  simpa [margin_profile_0_3] using h

private lemma margin_profile_2_1 : margin profile (2 : Fin 4) (1 : Fin 4) = 1 := by
  have h := margin_antisymmetric (P := profile) (a := (2 : Fin 4)) (b := (1 : Fin 4))
  simpa [margin_profile_1_2] using h

private lemma margin_profile_3_1 : margin profile (3 : Fin 4) (1 : Fin 4) = 1 := by
  have h := margin_antisymmetric (P := profile) (a := (3 : Fin 4)) (b := (1 : Fin 4))
  simpa [margin_profile_1_3] using h

private lemma margin_profile_3_2 : margin profile (3 : Fin 4) (2 : Fin 4) = 1 := by
  have h := margin_antisymmetric (P := profile) (a := (3 : Fin 4)) (b := (2 : Fin 4))
  simpa [margin_profile_2_3] using h

private lemma maxLoss_profile_3_le : maxLoss profile (3 : Fin 4) ≤ 0 := by
  refine maxLoss_le_of_forall_margin_le (P := profile) (a := (3 : Fin 4)) (k := 0) ?_
  intro b
  fin_cases b <;>
    simp [margin_profile_0_3, margin_profile_1_3, margin_profile_2_3, self_margin_zero]

private lemma maxLoss_profile_3_ge : (0 : Int) ≤ maxLoss profile (3 : Fin 4) := by
  have hle := margin_le_maxLoss (P := profile) (a := (3 : Fin 4)) (b := (3 : Fin 4))
  simpa [self_margin_zero] using hle

private lemma maxLoss_profile_3 : maxLoss profile (3 : Fin 4) = 0 :=
  le_antisymm maxLoss_profile_3_le maxLoss_profile_3_ge

private lemma maxLoss_profile_0_le : maxLoss profile (0 : Fin 4) ≤ 1 := by
  refine maxLoss_le_of_forall_margin_le (P := profile) (a := (0 : Fin 4)) (k := 1) ?_
  intro b
  fin_cases b <;>
    simp [margin_profile_1_0, margin_profile_2_0, margin_profile_3_0, self_margin_zero]

private lemma maxLoss_profile_0_ge : (1 : Int) ≤ maxLoss profile (0 : Fin 4) := by
  have hle := margin_le_maxLoss (P := profile) (a := (0 : Fin 4)) (b := (1 : Fin 4))
  simpa [margin_profile_1_0] using hle

private lemma maxLoss_profile_0 : maxLoss profile (0 : Fin 4) = 1 :=
  le_antisymm maxLoss_profile_0_le maxLoss_profile_0_ge

private lemma maxLoss_profile_1_le : maxLoss profile (1 : Fin 4) ≤ 1 := by
  refine maxLoss_le_of_forall_margin_le (P := profile) (a := (1 : Fin 4)) (k := 1) ?_
  intro b
  fin_cases b <;>
    simp [margin_profile_0_1, margin_profile_2_1, margin_profile_3_1, self_margin_zero]

private lemma maxLoss_profile_1_ge : (1 : Int) ≤ maxLoss profile (1 : Fin 4) := by
  have hle := margin_le_maxLoss (P := profile) (a := (1 : Fin 4)) (b := (2 : Fin 4))
  simpa [margin_profile_2_1] using hle

private lemma maxLoss_profile_1 : maxLoss profile (1 : Fin 4) = 1 :=
  le_antisymm maxLoss_profile_1_le maxLoss_profile_1_ge

private lemma maxLoss_profile_2_le : maxLoss profile (2 : Fin 4) ≤ 1 := by
  refine maxLoss_le_of_forall_margin_le (P := profile) (a := (2 : Fin 4)) (k := 1) ?_
  intro b
  fin_cases b <;>
    simp [margin_profile_0_2, margin_profile_1_2, margin_profile_3_2, self_margin_zero]

private lemma maxLoss_profile_2_ge : (1 : Int) ≤ maxLoss profile (2 : Fin 4) := by
  have hle := margin_le_maxLoss (P := profile) (a := (2 : Fin 4)) (b := (0 : Fin 4))
  simpa [margin_profile_0_2] using hle

private lemma maxLoss_profile_2 : maxLoss profile (2 : Fin 4) = 1 :=
  le_antisymm maxLoss_profile_2_le maxLoss_profile_2_ge

private lemma maxLoss_profile_ge_zero : ∀ a : Fin 4, (0 : Int) ≤ maxLoss profile a := by
  intro a
  have hle := margin_le_maxLoss (P := profile) (a := a) (b := a)
  simpa [self_margin_zero] using hle

private lemma minimaxScore_profile : minimaxScore profile = 0 := by
  have hA : (Finset.univ : Finset (Fin 4)).Nonempty := by simp
  have hmin_ge :
      (0 : Int) ≤ minimaxScore profile :=
    le_minimaxScore_of_forall (P := profile) (k := 0) hA maxLoss_profile_ge_zero
  have hmin_le :
      minimaxScore profile ≤ 0 := by
    have hle := minimaxScore_le_of_candidate (P := profile) (a := (3 : Fin 4))
    simpa [maxLoss_profile_3] using hle
  exact le_antisymm hmin_le hmin_ge

lemma minimax_profile_eq_singleton : minimax profile = ({3} : Finset (Fin 4)) := by
  have hnonempty : Nonempty (Fin 4) := inferInstance
  ext x
  fin_cases x
  · simp [minimax, hnonempty, minimaxScore_profile, maxLoss_profile_0]
  · simp [minimax, hnonempty, minimaxScore_profile, maxLoss_profile_1]
  · simp [minimax, hnonempty, minimaxScore_profile, maxLoss_profile_2]
  · simp [minimax, hnonempty, minimaxScore_profile, maxLoss_profile_3]

private lemma maxLoss_reverse_profile_3_le :
    maxLoss (reverse_profile profile) (3 : Fin 4) ≤ 1 := by
  refine maxLoss_le_of_forall_margin_le
    (P := reverse_profile profile) (a := (3 : Fin 4)) (k := 1) ?_
  intro b
  fin_cases b <;>
    simp [margin_reverse_eq, margin_profile_3_0, margin_profile_3_1, margin_profile_3_2,
      self_margin_zero]

private lemma maxLoss_reverse_profile_3_ge :
    (1 : Int) ≤ maxLoss (reverse_profile profile) (3 : Fin 4) := by
  have hle :=
    margin_le_maxLoss (P := reverse_profile profile) (a := (3 : Fin 4)) (b := (0 : Fin 4))
  simpa [margin_reverse_eq, margin_profile_3_0] using hle

private lemma maxLoss_reverse_profile_3 :
    maxLoss (reverse_profile profile) (3 : Fin 4) = 1 :=
  le_antisymm maxLoss_reverse_profile_3_le maxLoss_reverse_profile_3_ge

private lemma maxLoss_reverse_profile_ge_one :
    ∀ a : Fin 4, (1 : Int) ≤ maxLoss (reverse_profile profile) a := by
  intro a
  fin_cases a
  ·
    have hle :=
      margin_le_maxLoss (P := reverse_profile profile) (a := (0 : Fin 4)) (b := (2 : Fin 4))
    simpa [margin_reverse_eq, margin_profile_0_2] using hle
  ·
    have hle :=
      margin_le_maxLoss (P := reverse_profile profile) (a := (1 : Fin 4)) (b := (0 : Fin 4))
    simpa [margin_reverse_eq, margin_profile_1_0] using hle
  ·
    have hle :=
      margin_le_maxLoss (P := reverse_profile profile) (a := (2 : Fin 4)) (b := (1 : Fin 4))
    simpa [margin_reverse_eq, margin_profile_2_1] using hle
  ·
    have hle :=
      margin_le_maxLoss (P := reverse_profile profile) (a := (3 : Fin 4)) (b := (0 : Fin 4))
    simpa [margin_reverse_eq, margin_profile_3_0] using hle

private lemma minimaxScore_reverse_profile :
    minimaxScore (reverse_profile profile) = 1 := by
  have hA : (Finset.univ : Finset (Fin 4)).Nonempty := by simp
  have hmin_ge :
      (1 : Int) ≤ minimaxScore (reverse_profile profile) :=
    le_minimaxScore_of_forall (P := reverse_profile profile) (k := 1) hA
      maxLoss_reverse_profile_ge_one
  have hmin_le :
      minimaxScore (reverse_profile profile) ≤ 1 := by
    have hle :=
      minimaxScore_le_of_candidate (P := reverse_profile profile) (a := (3 : Fin 4))
    simpa [maxLoss_reverse_profile_3] using hle
  exact le_antisymm hmin_le hmin_ge

lemma reverse_profile_has_3 :
    (3 : Fin 4) ∈ minimax (reverse_profile profile) := by
  have hmem :
      (3 : Fin 4) ∈
        Finset.univ.filter (fun a : Fin 4 =>
          maxLoss (reverse_profile profile) a =
            minimaxScore (reverse_profile profile)) := by
    simp [maxLoss_reverse_profile_3, minimaxScore_reverse_profile]
  have hnonempty : Nonempty (Fin 4) := inferInstance
  simpa [minimax, hnonempty] using hmem

end MinimaxReversalCounterexample

theorem minimax_not_singletonReversalSymmetry : ¬ SingletonReversalSymmetry minimax := by
  intro h
  have hsingle :
      minimax MinimaxReversalCounterexample.profile = {3} :=
    MinimaxReversalCounterexample.minimax_profile_eq_singleton
  have hne : ∃ y : Fin 4, (3 : Fin 4) ≠ y := by
    exact ⟨0, by decide⟩
  have hnot :=
    h (P := MinimaxReversalCounterexample.profile) (x := (3 : Fin 4)) hne hsingle
  have hw :
      (3 : Fin 4) ∈ minimax (reverse_profile MinimaxReversalCounterexample.profile) :=
    MinimaxReversalCounterexample.reverse_profile_has_3
  exact hnot hw

end SocialChoice
