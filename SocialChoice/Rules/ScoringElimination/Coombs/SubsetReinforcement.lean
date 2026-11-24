import Mathlib.Tactic
import Mathlib.Tactic.FinCases
import SocialChoice.Axioms.Implications
import SocialChoice.Axioms.Participation
import SocialChoice.ListBallot
import SocialChoice.ListBallotProfiles
import SocialChoice.Margin
import SocialChoice.Rules.ScoringElimination.Basic
import SocialChoice.Rules.ScoringElimination.Coombs.CondorcetLoser
import SocialChoice.Rules.ScoringElimination.Coombs.Defs
import SocialChoice.Rules.ScoringRules.Veto.Common

namespace SocialChoice

open Finset

/-!
# Coombs fails subset reinforcement

Counterexample with 3 candidates and two disjoint electorates:

Subprofile 1 (2 voters):
  1 > 0 > 2
  2 > 0 > 1
Coombs selects {0,1,2}.

Subprofile 2 (2 voters):
  1 > 2 > 0
  2 > 0 > 1
Coombs selects {1,2}.

Full profile (4 voters):
  1 > 0 > 2
  1 > 2 > 0
  2 > 0 > 1
  2 > 0 > 1
Coombs selects {2}.

Thus 1 is a winner in both subprofiles but not in the full profile.
-/

namespace CoombsSubsetReinforcementCounterexample

def ballot102 : ListBallot 3 := ListBallot.mk' [1, 0, 2]
def ballot120 : ListBallot 3 := ListBallot.mk' [1, 2, 0]
def ballot201 : ListBallot 3 := ListBallot.mk' [2, 0, 1]

def ballots4 : Fin 4 → ListBallot 3
  | 0 => ballot102
  | 1 => ballot201
  | 2 => ballot120
  | 3 => ballot201

def voters1 : Finset (Fin 4) := {0, 1}
def voters2 : Finset (Fin 4) := {2, 3}

def ballots1 (v : Electorate (Fin 4) voters1) : ListBallot 3 := ballots4 v.1
def ballots2 (v : Electorate (Fin 4) voters2) : ListBallot 3 := ballots4 v.1
def ballotsAll (v : Electorate (Fin 4) (voters1 ∪ voters2)) : ListBallot 3 := ballots4 v.1

noncomputable def profile1 : Profile (Electorate (Fin 4) voters1) (Fin 3) :=
  profileOfListBallots ballots1

noncomputable def profile2 : Profile (Electorate (Fin 4) voters2) (Fin 3) :=
  profileOfListBallots ballots2

noncomputable def profileAll :
    Profile (Electorate (Fin 4) (voters1 ∪ voters2)) (Fin 3) :=
  profileOfListBallots ballotsAll

lemma voters1_disjoint_voters2 : Disjoint voters1 voters2 := by
  decide

lemma restrict_profileAll_voters1 :
    restrictElectorate profileAll voters1
        (by intro x hx; exact Finset.mem_union.mpr (Or.inl hx)) =
      profile1 := by
  rfl

lemma restrict_profileAll_voters2 :
    restrictElectorate profileAll voters2
        (by intro x hx; exact Finset.mem_union.mpr (Or.inr hx)) =
      profile2 := by
  rfl

@[reducible] def scoreVec : Nat → Int := fun r => vetoScore (Fintype.card (Fin 3)) r

lemma lowestScoring_profile1_has_2 :
    (2 : Fin 3) ∈ lowestScoring profile1 scoreVec := by
  decide

lemma lowestScoring_profile2_has_0 :
    (0 : Fin 3) ∈ lowestScoring profile2 scoreVec := by
  decide

lemma lowestScoring_profileAll_eq_singleton_1 :
    lowestScoring profileAll scoreVec = ({1} : Finset (Fin 3)) := by
  decide

/-! ## Pairwise margins -/

lemma margin_profile1_1_0 :
    margin profile1 (1 : Fin 3) (0 : Fin 3) = (0 : Int) := by
  rw [profile1, margin_profileOfListBallots]
  decide

lemma margin_profile2_1_2 :
    margin profile2 (1 : Fin 3) (2 : Fin 3) = (0 : Int) := by
  rw [profile2, margin_profileOfListBallots]
  decide

def cand0_2 : {x : Fin 3 // x ≠ (2 : Fin 3)} := ⟨0, by decide⟩
def cand1_2 : {x : Fin 3 // x ≠ (2 : Fin 3)} := ⟨1, by decide⟩
def cand1_0 : {x : Fin 3 // x ≠ (0 : Fin 3)} := ⟨1, by decide⟩
def cand2_0 : {x : Fin 3 // x ≠ (0 : Fin 3)} := ⟨2, by decide⟩

lemma coombs_profile1_has_1 : (1 : Fin 3) ∈ coombs profile1 := by
  classical
  have hcard : ¬ Fintype.card (Fin 3) ≤ 1 := by decide
  have haux :=
    scoringEliminationAux_eq_biUnion_of_not_card_le_one
      (score := vetoScore) (P := profile1) (hcard := hcard)
  have haux' :
      scoringEliminationAux vetoScore (Fin 3) profile1 =
        (lowestScoring profile1 scoreVec).biUnion
          (fun c => liftFinset (scoringEliminationAux vetoScore _ (restrictProfile profile1 c))) := by
    exact haux
  have hcoombs :
      coombs profile1 = scoringEliminationAux vetoScore (Fin 3) profile1 := by
    classical
    simpa [coombs, scoringEliminationRule] using
      (scoringEliminationAux_decidableEq_congr (score := vetoScore) (P := profile1)
        (inst1 := Classical.decEq (Fin 3)) (inst2 := inferInstance))
  have hcard' : Fintype.card {x : Fin 3 // x ≠ (2 : Fin 3)} = 2 := by
    simp [card_subtype_ne_eq (2 : Fin 3)]
  have hiff :
      cand1_2 ∈ coombs (restrictProfile profile1 (2 : Fin 3)) ↔
        0 ≤ margin (restrictProfile profile1 (2 : Fin 3)) cand1_2 cand0_2 := by
    simpa [cand1_2, cand0_2] using
      (coombs_of_card_two (P := restrictProfile profile1 (2 : Fin 3)) (hcard := hcard')
        (a := cand1_2) (b := cand0_2) (hab := by decide))
  have hmargin :
      margin (restrictProfile profile1 (2 : Fin 3)) cand1_2 cand0_2 =
        margin profile1 (1 : Fin 3) (0 : Fin 3) := by
    simpa [cand1_2, cand0_2] using
      (margin_eq_margin_restrictProfile (P := profile1) (c := (2 : Fin 3))
        (a := cand1_2) (b := cand0_2)).symm
  have hmargin_val :
      margin (restrictProfile profile1 (2 : Fin 3)) cand1_2 cand0_2 = (0 : Int) := by
    simpa [hmargin] using margin_profile1_1_0
  have hle : 0 ≤ margin (restrictProfile profile1 (2 : Fin 3)) cand1_2 cand0_2 := by
    simp [hmargin_val]
  have hmem_sub : cand1_2 ∈ coombs (restrictProfile profile1 (2 : Fin 3)) := hiff.mpr hle
  have hcoombs_sub :
      coombs (restrictProfile profile1 (2 : Fin 3)) =
        scoringEliminationAux vetoScore _ (restrictProfile profile1 (2 : Fin 3)) := by
    classical
    simpa [coombs, scoringEliminationRule] using
      (scoringEliminationAux_decidableEq_congr (score := vetoScore)
        (P := restrictProfile profile1 (2 : Fin 3))
        (inst1 := Classical.decEq _) (inst2 := inferInstance))
  have hmem_sub' :
      cand1_2 ∈ scoringEliminationAux vetoScore _ (restrictProfile profile1 (2 : Fin 3)) := by
    simpa [hcoombs_sub] using hmem_sub
  have hmem_lift :
      (1 : Fin 3) ∈
        liftFinset (scoringEliminationAux vetoScore _ (restrictProfile profile1 (2 : Fin 3))) := by
    exact (mem_liftFinset_iff_subtype
      (s := scoringEliminationAux vetoScore _ (restrictProfile profile1 (2 : Fin 3)))
      (x := (1 : Fin 3))).2 ⟨by decide, hmem_sub'⟩
  have hmem_union :
      (1 : Fin 3) ∈
        (lowestScoring profile1 scoreVec).biUnion
          (fun c => liftFinset (scoringEliminationAux vetoScore _ (restrictProfile profile1 c))) := by
    refine Finset.mem_biUnion.mpr ?_
    refine ⟨(2 : Fin 3), lowestScoring_profile1_has_2, ?_⟩
    simpa using hmem_lift
  have hmem_aux : (1 : Fin 3) ∈ scoringEliminationAux vetoScore (Fin 3) profile1 := by
    simpa [haux'] using hmem_union
  simpa [hcoombs] using hmem_aux

lemma coombs_profile2_has_1 : (1 : Fin 3) ∈ coombs profile2 := by
  classical
  have hcard : ¬ Fintype.card (Fin 3) ≤ 1 := by decide
  have haux :=
    scoringEliminationAux_eq_biUnion_of_not_card_le_one
      (score := vetoScore) (P := profile2) (hcard := hcard)
  have haux' :
      scoringEliminationAux vetoScore (Fin 3) profile2 =
        (lowestScoring profile2 scoreVec).biUnion
          (fun c => liftFinset (scoringEliminationAux vetoScore _ (restrictProfile profile2 c))) := by
    exact haux
  have hcoombs :
      coombs profile2 = scoringEliminationAux vetoScore (Fin 3) profile2 := by
    classical
    simpa [coombs, scoringEliminationRule] using
      (scoringEliminationAux_decidableEq_congr (score := vetoScore) (P := profile2)
        (inst1 := Classical.decEq (Fin 3)) (inst2 := inferInstance))
  have hcard' : Fintype.card {x : Fin 3 // x ≠ (0 : Fin 3)} = 2 := by
    simp [card_subtype_ne_eq (0 : Fin 3)]
  have hiff :
      cand1_0 ∈ coombs (restrictProfile profile2 (0 : Fin 3)) ↔
        0 ≤ margin (restrictProfile profile2 (0 : Fin 3)) cand1_0 cand2_0 := by
    simpa [cand1_0, cand2_0] using
      (coombs_of_card_two (P := restrictProfile profile2 (0 : Fin 3)) (hcard := hcard')
        (a := cand1_0) (b := cand2_0) (hab := by decide))
  have hmargin :
      margin (restrictProfile profile2 (0 : Fin 3)) cand1_0 cand2_0 =
        margin profile2 (1 : Fin 3) (2 : Fin 3) := by
    simpa [cand1_0, cand2_0] using
      (margin_eq_margin_restrictProfile (P := profile2) (c := (0 : Fin 3))
        (a := cand1_0) (b := cand2_0)).symm
  have hmargin_val :
      margin (restrictProfile profile2 (0 : Fin 3)) cand1_0 cand2_0 = (0 : Int) := by
    simpa [hmargin] using margin_profile2_1_2
  have hle : 0 ≤ margin (restrictProfile profile2 (0 : Fin 3)) cand1_0 cand2_0 := by
    simp [hmargin_val]
  have hmem_sub : cand1_0 ∈ coombs (restrictProfile profile2 (0 : Fin 3)) := hiff.mpr hle
  have hcoombs_sub :
      coombs (restrictProfile profile2 (0 : Fin 3)) =
        scoringEliminationAux vetoScore _ (restrictProfile profile2 (0 : Fin 3)) := by
    classical
    simpa [coombs, scoringEliminationRule] using
      (scoringEliminationAux_decidableEq_congr (score := vetoScore)
        (P := restrictProfile profile2 (0 : Fin 3))
        (inst1 := Classical.decEq _) (inst2 := inferInstance))
  have hmem_sub' :
      cand1_0 ∈ scoringEliminationAux vetoScore _ (restrictProfile profile2 (0 : Fin 3)) := by
    simpa [hcoombs_sub] using hmem_sub
  have hmem_lift :
      (1 : Fin 3) ∈
        liftFinset (scoringEliminationAux vetoScore _ (restrictProfile profile2 (0 : Fin 3))) := by
    exact (mem_liftFinset_iff_subtype
      (s := scoringEliminationAux vetoScore _ (restrictProfile profile2 (0 : Fin 3)))
      (x := (1 : Fin 3))).2 ⟨by decide, hmem_sub'⟩
  have hmem_union :
      (1 : Fin 3) ∈
        (lowestScoring profile2 scoreVec).biUnion
          (fun c => liftFinset (scoringEliminationAux vetoScore _ (restrictProfile profile2 c))) := by
    refine Finset.mem_biUnion.mpr ?_
    refine ⟨(0 : Fin 3), lowestScoring_profile2_has_0, ?_⟩
    simpa using hmem_lift
  have hmem_aux : (1 : Fin 3) ∈ scoringEliminationAux vetoScore (Fin 3) profile2 := by
    simpa [haux'] using hmem_union
  simpa [hcoombs] using hmem_aux

lemma coombs_profileAll_not_1 : (1 : Fin 3) ∉ coombs profileAll := by
  classical
  have hcard : ¬ Fintype.card (Fin 3) ≤ 1 := by decide
  have haux :=
    scoringEliminationAux_eq_biUnion_of_not_card_le_one
      (score := vetoScore) (P := profileAll) (hcard := hcard)
  have haux' :
      scoringEliminationAux vetoScore (Fin 3) profileAll =
        (lowestScoring profileAll scoreVec).biUnion
          (fun c => liftFinset (scoringEliminationAux vetoScore _ (restrictProfile profileAll c))) := by
    exact haux
  have haux'' :
      scoringEliminationAux vetoScore (Fin 3) profileAll =
        ({1} : Finset (Fin 3)).biUnion
          (fun c => liftFinset (scoringEliminationAux vetoScore _ (restrictProfile profileAll c))) := by
    simpa [lowestScoring_profileAll_eq_singleton_1] using haux'
  have hcoombs :
      coombs profileAll = scoringEliminationAux vetoScore (Fin 3) profileAll := by
    classical
    simpa [coombs, scoringEliminationRule] using
      (scoringEliminationAux_decidableEq_congr (score := vetoScore) (P := profileAll)
        (inst1 := Classical.decEq (Fin 3)) (inst2 := inferInstance))
  intro hmem
  have hmem' :
      (1 : Fin 3) ∈
        ({1} : Finset (Fin 3)).biUnion
          (fun c => liftFinset (scoringEliminationAux vetoScore _ (restrictProfile profileAll c))) := by
    simpa [hcoombs, haux''] using hmem
  rcases Finset.mem_biUnion.mp hmem' with ⟨c, hcL, hmem_c⟩
  have hc1 : c = (1 : Fin 3) := by
    simpa using (Finset.mem_singleton.mp hcL)
  subst hc1
  have hnot :
      (1 : Fin 3) ∉
        liftFinset (scoringEliminationAux vetoScore _ (restrictProfile profileAll (1 : Fin 3))) := by
    exact not_mem_liftFinset_removed
      (s := scoringEliminationAux vetoScore _ (restrictProfile profileAll (1 : Fin 3)))
  exact hnot hmem_c

theorem coombs_subsetReinforcement_counterexample_sets :
    ¬ (coombs profile1 ∩ coombs profile2 ⊆ coombs profileAll) := by
  intro hsubset
  have hmem : (1 : Fin 3) ∈ coombs profile1 ∩ coombs profile2 := by
    exact Finset.mem_inter.mpr ⟨coombs_profile1_has_1, coombs_profile2_has_1⟩
  have hmem' := hsubset hmem
  exact coombs_profileAll_not_1 hmem'

end CoombsSubsetReinforcementCounterexample

end SocialChoice
