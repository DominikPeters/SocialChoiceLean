import Mathlib.Tactic
import Mathlib.Tactic.FinCases
import SocialChoice.Axioms.Majority
import SocialChoice.ListBallot
import SocialChoice.Rules.PluralityWithRunoff.Defs

namespace SocialChoice

open Finset

/-!
# Plurality with Runoff fails the mutual majority criterion

We use a five-voter profile with five candidates. The strict majority
{0,1,2} ranks every candidate in {0,1,2} above {3,4}, but candidate 3
can win a runoff against 4.
-/

namespace PluralityWithRunoffMutualMajorityCounterexample

def ballot01234 : ListBallot 5 := ListBallot.mk' [0, 1, 2, 3, 4]
def ballot12034 : ListBallot 5 := ListBallot.mk' [1, 2, 0, 3, 4]
def ballot20134 : ListBallot 5 := ListBallot.mk' [2, 0, 1, 3, 4]
def ballot34012 : ListBallot 5 := ListBallot.mk' [3, 4, 0, 1, 2]
def ballot43012 : ListBallot 5 := ListBallot.mk' [4, 3, 0, 1, 2]

def ballots : Fin 5 → ListBallot 5
  | 0 => ballot01234
  | 1 => ballot12034
  | 2 => ballot20134
  | 3 => ballot34012
  | 4 => ballot43012
  | _ => ballot01234

noncomputable def profile : Profile (Fin 5) (Fin 5) :=
  profileOfListBallots ballots

private lemma plurality_profile_eq :
    plurality profile = (Finset.univ : Finset (Fin 5)) := by
  rw [profile]
  simp only [plurality, topCount, votersTop_eq_filter_isTopOfList]
  decide

private lemma pair_34_mem_pairs :
    ({3, 4} : Finset (Fin 5)) ∈ pluralityWithRunoffPairs profile := by
  have hS : (plurality profile).card ≥ 2 := by
    simp [plurality_profile_eq]
  have hsubset : ({3, 4} : Finset (Fin 5)) ⊆ plurality profile := by
    intro x hx
    simp [plurality_profile_eq]
  have hcardpair : ({3, 4} : Finset (Fin 5)).card = 2 := by
    simp
  have hmem : ({3, 4} : Finset (Fin 5)) ∈ (plurality profile).powersetCard 2 := by
    exact Finset.mem_powersetCard.mpr ⟨hsubset, hcardpair⟩
  simpa [pluralityWithRunoffPairs, hS] using hmem

private lemma margin_profile_3_4 : margin profile (3 : Fin 5) (4 : Fin 5) = 3 := by
  rw [profile, margin_profileOfListBallots]
  decide

private lemma pluralityWithRunoff_profile_has_3 :
    (3 : Fin 5) ∈ pluralityWithRunoff profile :=
  (mem_pluralityWithRunoff_iff profile 3 (by decide)).2
    ⟨4, pair_34_mem_pairs, by simp [margin_profile_3_4]⟩

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

theorem pluralityWithRunoff_not_mutualMajorityCriterion :
    ¬ MutualMajorityCriterion pluralityWithRunoff := by
  intro hmut
  have hsubset :
      pluralityWithRunoff profile ⊆ T :=
    hmut (P := profile) (S := S) (T := T) strictMajority_S T_nonempty prefers_T_over_Tc
  have hwin : (3 : Fin 5) ∈ pluralityWithRunoff profile :=
    pluralityWithRunoff_profile_has_3
  have hnot : (3 : Fin 5) ∉ T := by
    simp [T]
  exact hnot (hsubset hwin)

end PluralityWithRunoffMutualMajorityCounterexample

end SocialChoice
