import Mathlib.Tactic
import Mathlib.Tactic.FinCases
import SocialChoice.Axioms.Majority
import SocialChoice.ListBallot
import SocialChoice.Rules.Black.Defs

namespace SocialChoice

open Finset

/-!
# Black fails the mutual majority criterion

We use a five-voter profile with five candidates. There is no Condorcet
winner and the Borda winners are {0,1,2,3}, so 3 is a Black winner even
though a strict majority ranks {0,1,2} above {3,4}.
-/

namespace BlackMutualMajorityCounterexample

def ballot01234 : ListBallot 5 := ListBallot.mk' [0, 1, 2, 3, 4]
def ballot12034 : ListBallot 5 := ListBallot.mk' [1, 2, 0, 3, 4]
def ballot20134 : ListBallot 5 := ListBallot.mk' [2, 0, 1, 3, 4]
def ballot34012 : ListBallot 5 := ListBallot.mk' [3, 4, 0, 1, 2]
def ballot34210 : ListBallot 5 := ListBallot.mk' [3, 4, 2, 1, 0]

def ballots : Fin 5 → ListBallot 5
  | 0 => ballot01234
  | 1 => ballot12034
  | 2 => ballot20134
  | 3 => ballot34012
  | 4 => ballot34210
  | _ => ballot01234

noncomputable def profile : Profile (Fin 5) (Fin 5) :=
  profileOfListBallots ballots

private lemma margin_profile_0_2 : margin profile (0 : Fin 5) (2 : Fin 5) = -1 := by
  rw [profile, margin_eq_marginList]; rfl

private lemma margin_profile_1_0 : margin profile (1 : Fin 5) (0 : Fin 5) = -1 := by
  rw [profile, margin_eq_marginList]; rfl

private lemma margin_profile_2_1 : margin profile (2 : Fin 5) (1 : Fin 5) = -1 := by
  rw [profile, margin_eq_marginList]; rfl

private lemma margin_profile_3_0 : margin profile (3 : Fin 5) (0 : Fin 5) = -1 := by
  rw [profile, margin_eq_marginList]; rfl

private lemma margin_profile_4_3 : margin profile (4 : Fin 5) (3 : Fin 5) = -5 := by
  rw [profile, margin_eq_marginList]; rfl

private lemma no_condorcet_profile : ¬ ∃ x, CondorcetWinner profile x := by
  intro h
  rcases h with ⟨x, hx⟩
  have hx' := (CondorcetWinner_iff_margin_pos (P := profile) x).1 hx
  fin_cases x
  · have hpos := hx' (2 : Fin 5) (by decide)
    simp [margin_pos, margin_profile_0_2] at hpos
  · have hpos := hx' (0 : Fin 5) (by decide)
    simp [margin_pos, margin_profile_1_0] at hpos
  · have hpos := hx' (1 : Fin 5) (by decide)
    simp [margin_pos, margin_profile_2_1] at hpos
  · have hpos := hx' (0 : Fin 5) (by decide)
    simp [margin_pos, margin_profile_3_0] at hpos
  · have hpos := hx' (3 : Fin 5) (by decide)
    simp [margin_pos, margin_profile_4_3] at hpos

private lemma borda_profile : borda profile = ({0, 1, 2, 3} : Finset (Fin 5)) := by
  classical
  ext x
  fin_cases x <;> decide

private lemma black_profile : black profile = ({0, 1, 2, 3} : Finset (Fin 5)) := by
  have h : ¬ ∃ x, CondorcetWinner profile x := no_condorcet_profile
  simpa [black, h] using borda_profile

private def S : Finset (Fin 5) := {0, 1, 2}
private def T : Finset (Fin 5) := {0, 1, 2}

private lemma strictMajority_S : StrictMajority S := by
  unfold StrictMajority S
  simp

private lemma T_nonempty : T.Nonempty := by
  simp [T]

private lemma prefers_T_over_Tc :
    ∀ v ∈ S, ∀ a ∈ T, ∀ b ∉ T, Prefers profile v a b := by
  simp only [S, T, profile, prefers_iff_prefersInList]
  decide

theorem black_not_mutualMajorityCriterion : ¬ MutualMajorityCriterion black := by
  intro hmut
  have hsubset :
      black profile ⊆ T :=
    hmut (P := profile) (S := S) (T := T) strictMajority_S T_nonempty prefers_T_over_Tc
  have hwin : (3 : Fin 5) ∈ black profile := by
    simp [black_profile]
  have hnot : (3 : Fin 5) ∉ T := by
    simp [T]
  exact hnot (hsubset hwin)

end BlackMutualMajorityCounterexample

end SocialChoice
