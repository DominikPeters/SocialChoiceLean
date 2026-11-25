import Mathlib.Tactic
import Mathlib.Tactic.FinCases
import SocialChoice.Axioms.Monotonicity
import SocialChoice.ListBallot
import SocialChoice.Rules.PluralityWithRunoff.EqualsIRVForThreeCandidates
import SocialChoice.Rules.PluralityWithRunoff.CondorcetLoser
import SocialChoice.Rules.ScoringElimination.InstantRunoffVoting.Defs

namespace SocialChoice

open Finset

/-!
# Plurality with Runoff (and IRV) fails monotonicity

We use a 17-voter profile with three candidates. Candidate 0 wins plurality with
runoff; after two voters lift 0 to the top (without changing the relative order
of the other candidates), candidate 0 loses.
-/

namespace PluralityWithRunoffMonotonicityCounterexample

def ballot012 : ListBallot 3 := ListBallot.mk' [0, 1, 2]
def ballot102 : ListBallot 3 := ListBallot.mk' [1, 0, 2]
def ballot210 : ListBallot 3 := ListBallot.mk' [2, 1, 0]
def ballot021 : ListBallot 3 := ListBallot.mk' [0, 2, 1]

def ballots : Fin 17 -> ListBallot 3
  | 0 => ballot012
  | 1 => ballot012
  | 2 => ballot012
  | 3 => ballot012
  | 4 => ballot012
  | 5 => ballot012
  | 6 => ballot102
  | 7 => ballot102
  | 8 => ballot102
  | 9 => ballot102
  | 10 => ballot102
  | 11 => ballot210
  | 12 => ballot210
  | 13 => ballot210
  | 14 => ballot210
  | 15 => ballot210
  | 16 => ballot210
  | _ => ballot210

def ballots' : Fin 17 -> ListBallot 3
  | 0 => ballot012
  | 1 => ballot012
  | 2 => ballot012
  | 3 => ballot012
  | 4 => ballot012
  | 5 => ballot012
  | 6 => ballot102
  | 7 => ballot102
  | 8 => ballot102
  | 9 => ballot102
  | 10 => ballot102
  | 11 => ballot210
  | 12 => ballot210
  | 13 => ballot210
  | 14 => ballot210
  | 15 => ballot021
  | 16 => ballot021
  | _ => ballot021

noncomputable def profile : Profile (Fin 17) (Fin 3) :=
  profileOfListBallots ballots

noncomputable def profile' : Profile (Fin 17) (Fin 3) :=
  profileOfListBallots ballots'

private lemma plurality_profile_eq : plurality profile = ({0, 2} : Finset (Fin 3)) := by
  rw [profile]
  simp only [plurality, topCount, votersTop_eq_filter_isTopOfList]
  decide

private lemma plurality_profile'_eq : plurality profile' = ({0} : Finset (Fin 3)) := by
  rw [profile']
  simp only [plurality, topCount, votersTop_eq_filter_isTopOfList]
  decide

private lemma margin_profile_0_2 : margin profile (0 : Fin 3) (2 : Fin 3) = 5 := by
  rw [profile, margin_profileOfListBallots]
  decide

private lemma margin_profile'_0_1 : margin profile' (0 : Fin 3) (1 : Fin 3) = -1 := by
  rw [profile', margin_profileOfListBallots]
  decide

private lemma pair_02_mem_pairs :
    ({0, 2} : Finset (Fin 3)) ∈
      pluralityWithRunoffPairs profile := by
  have hS : (plurality profile).card >= 2 := by
    simp [plurality_profile_eq]
  have hsubset : ({0, 2} : Finset (Fin 3)) ⊆ plurality profile := by
    intro x hx
    simpa [plurality_profile_eq] using hx
  have hcardpair : ({0, 2} : Finset (Fin 3)).card = 2 := by
    simp
  have hmem : ({0, 2} : Finset (Fin 3)) ∈ (plurality profile).powersetCard 2 := by
    exact Finset.mem_powersetCard.mpr ⟨hsubset, hcardpair⟩
  simpa [pluralityWithRunoffPairs, hS] using hmem

private lemma secondPluralitySet_profile' :
    secondPluralitySet profile' (plurality profile') = ({1} : Finset (Fin 3)) := by
  rw [plurality_profile'_eq, profile']
  simp [secondPluralitySet, topCount, votersTop_eq_filter_isTopOfList]
  decide

private lemma pluralityWithRunoffPairs_profile' :
    pluralityWithRunoffPairs profile' =
      ({({0, 1} : Finset (Fin 3))} : Finset (Finset (Fin 3))) := by
  have hT :
      secondPluralitySet profile' ({0} : Finset (Fin 3)) = ({1} : Finset (Fin 3)) := by
    simpa [plurality_profile'_eq] using secondPluralitySet_profile'
  calc
    pluralityWithRunoffPairs profile' =
        (({0} : Finset (Fin 3)).product ({1} : Finset (Fin 3))).image
          (fun p => ({p.1, p.2} : Finset (Fin 3))) := by
        simp [pluralityWithRunoffPairs, plurality_profile'_eq, hT]
    _ = ({({0, 1} : Finset (Fin 3))} : Finset (Finset (Fin 3))) := by
        simp

private lemma pluralityWithRunoff_profile_has_0 :
    (0 : Fin 3) ∈ pluralityWithRunoff profile :=
  (mem_pluralityWithRunoff_iff profile 0 (by decide)).2
    ⟨2, pair_02_mem_pairs, by simp [margin_profile_0_2]⟩

private lemma pluralityWithRunoff_profile'_not_0 :
    (0 : Fin 3) ∉ pluralityWithRunoff profile' := by
  intro hmem
  obtain ⟨y, hyPair, hmargin⟩ := (mem_pluralityWithRunoff_iff profile' 0 (by decide)).1 hmem
  rw [pluralityWithRunoffPairs_profile'] at hyPair
  fin_cases y
  · exact absurd hyPair (by decide)
  · simp [margin_profile'_0_1] at hmargin
  · exact absurd hyPair (by decide)

private lemma irv_profile_has_0 :
    (0 : Fin 3) ∈ instantRunoffVoting profile := by
  have hIRV :
      instantRunoffVoting profile = pluralityWithRunoff profile := by
    simpa using
      (instantRunoffVoting_eq_pluralityWithRunoff_of_card_le_three
        (V := Fin 17) (A := Fin 3) (hcard := by decide) (P := profile))
  simpa [hIRV] using pluralityWithRunoff_profile_has_0

private lemma irv_profile'_not_0 :
    (0 : Fin 3) ∉ instantRunoffVoting profile' := by
  have hIRV :
      instantRunoffVoting profile' = pluralityWithRunoff profile' := by
    simpa using
      (instantRunoffVoting_eq_pluralityWithRunoff_of_card_le_three
        (V := Fin 17) (A := Fin 3) (hcard := by decide) (P := profile'))
  simpa [hIRV] using pluralityWithRunoff_profile'_not_0

private lemma simpleLift_profile : simpleLift profile' profile (0 : Fin 3) := by
  simp only [simpleLift, profile, profile', prefers_iff_prefersInList]
  decide

theorem instantRunoffVoting_not_monotonicity : ¬ Monotonicity instantRunoffVoting := by
  intro hmono
  have hx : (0 : Fin 3) ∈ instantRunoffVoting profile := irv_profile_has_0
  have hlift : simpleLift profile' profile (0 : Fin 3) := simpleLift_profile
  have hx' : (0 : Fin 3) ∈ instantRunoffVoting profile' := hmono profile profile' 0 hx hlift
  exact irv_profile'_not_0 hx'

theorem pluralityWithRunoff_not_monotonicity : ¬ Monotonicity pluralityWithRunoff := by
  intro hmono
  have hx : (0 : Fin 3) ∈ pluralityWithRunoff profile := pluralityWithRunoff_profile_has_0
  have hlift : simpleLift profile' profile (0 : Fin 3) := simpleLift_profile
  have hx' : (0 : Fin 3) ∈ pluralityWithRunoff profile' := hmono profile profile' 0 hx hlift
  exact pluralityWithRunoff_profile'_not_0 hx'

end PluralityWithRunoffMonotonicityCounterexample

end SocialChoice
