import Mathlib.Tactic
import Mathlib.Tactic.FinCases
import SocialChoice.Axioms.Smith
import SocialChoice.ListBallot
import SocialChoice.Rules.Black.Defs
import SocialChoice.Rules.TopCycle.Defs

namespace SocialChoice

open Finset

/-!
## Black fails the Smith criterion

Counterexample with 4 candidates and 8 voters (3+1+3+1 blocks):
  3 voters: 2 ≻ 1 ≻ 0 ≻ 3
  1 voter : 2 ≻ 3 ≻ 1 ≻ 0
  3 voters: 3 ≻ 1 ≻ 0 ≻ 2
  1 voter : 3 ≻ 2 ≻ 1 ≻ 0
The Smith set is {2,3}, but Black returns {1,2,3}.
-/

namespace BlackSmithCounterexample

def ballot2103 : ListBallot 4 := ListBallot.mk' [2, 1, 0, 3]
def ballot2310 : ListBallot 4 := ListBallot.mk' [2, 3, 1, 0]
def ballot3102 : ListBallot 4 := ListBallot.mk' [3, 1, 0, 2]
def ballot3210 : ListBallot 4 := ListBallot.mk' [3, 2, 1, 0]

def ballots : Fin 8 → ListBallot 4
  | 0 => ballot2103
  | 1 => ballot2103
  | 2 => ballot2103
  | 3 => ballot2310
  | 4 => ballot3102
  | 5 => ballot3102
  | 6 => ballot3102
  | 7 => ballot3210
  | _ => ballot3210

noncomputable def profile : Profile (Fin 8) (Fin 4) :=
  profileOfListBallots ballots

def smithSet : Finset (Fin 4) := {2, 3}

private lemma margin_pos_profile_2_0 : margin_pos profile (2 : Fin 4) (0 : Fin 4) := by
  rw [profile, margin_pos_iff_marginList_pos]; decide

private lemma margin_pos_profile_2_1 : margin_pos profile (2 : Fin 4) (1 : Fin 4) := by
  rw [profile, margin_pos_iff_marginList_pos]; decide

private lemma margin_pos_profile_3_0 : margin_pos profile (3 : Fin 4) (0 : Fin 4) := by
  rw [profile, margin_pos_iff_marginList_pos]; decide

private lemma margin_pos_profile_3_1 : margin_pos profile (3 : Fin 4) (1 : Fin 4) := by
  rw [profile, margin_pos_iff_marginList_pos]; decide

lemma dominatesSet_profile_smithSet : dominatesSet profile smithSet := by
  classical
  refine ⟨?_, ?_⟩
  · simp [smithSet]
  · intro a ha b hb
    have ha' : a = (2 : Fin 4) ∨ a = (3 : Fin 4) := by
      simpa [smithSet] using ha
    rcases ha' with rfl | rfl
    · fin_cases b
      · exact margin_pos_profile_2_0
      · exact margin_pos_profile_2_1
      · simp [smithSet] at hb
      · simp [smithSet] at hb
    · fin_cases b
      · exact margin_pos_profile_3_0
      · exact margin_pos_profile_3_1
      · simp [smithSet] at hb
      · simp [smithSet] at hb

lemma topCycle_profile_subset : topCycle profile ⊆ smithSet := by
  classical
  have hA : Nonempty (Fin 4) := inferInstance
  have hsubset : topCycleSet (P := profile) ⊆ smithSet :=
    topCycleSet_subset_of_dominates (P := profile) dominatesSet_profile_smithSet
  simpa [topCycle, hA] using hsubset

lemma one_not_mem_topCycle : (1 : Fin 4) ∉ topCycle profile := by
  have hsubset := topCycle_profile_subset
  intro hmem
  have : (1 : Fin 4) ∈ smithSet := hsubset hmem
  simp [smithSet] at this

lemma no_condorcet_profile : ¬ ∃ x, CondorcetWinner profile x := by
  simp only [profile, CondorcetWinner_iff_marginList]
  decide

lemma borda_profile : borda profile = ({1, 2, 3} : Finset (Fin 4)) := by
  ext x
  fin_cases x <;> decide

lemma black_profile : black profile = ({1, 2, 3} : Finset (Fin 4)) := by
  have h : ¬ ∃ x, CondorcetWinner profile x := no_condorcet_profile
  simpa [black, h] using borda_profile

end BlackSmithCounterexample

open BlackSmithCounterexample

theorem black_not_smithCriterion : ¬ SmithCriterion black := by
  intro hsmith
  have hsubset := hsmith (P := profile)
  have hmem : (1 : Fin 4) ∈ black profile := by
    simp [black_profile]
  have hmem' : (1 : Fin 4) ∈ topCycle profile := hsubset hmem
  exact (one_not_mem_topCycle hmem').elim

end SocialChoice
