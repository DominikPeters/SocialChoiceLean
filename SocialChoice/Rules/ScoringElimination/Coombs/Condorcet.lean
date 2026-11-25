import Mathlib.Tactic
import Mathlib.Tactic.FinCases
import SocialChoice.Axioms.Condorcet
import SocialChoice.ListBallot
import SocialChoice.Profile
import SocialChoice.Rules.ScoringElimination.Basic
import SocialChoice.Rules.ScoringElimination.Coombs.Defs
import SocialChoice.Rules.ScoringRules.Veto.Common

namespace SocialChoice

open Finset

/-!
# Coombs fails Condorcet consistency

We use a 13-voter profile with three candidates, where candidate 1 is the
Condorcet winner, but Coombs returns candidate 0.

Example taken from
Minimal Voting Paradoxes
Felix Brandt, Marie Matthäus, Christian Saile
-/

namespace CoombsCondorcetCounterexample

def ballot021 : ListBallot 3 := ListBallot.mk' [0, 2, 1]
def ballot120 : ListBallot 3 := ListBallot.mk' [1, 2, 0]
def ballot102 : ListBallot 3 := ListBallot.mk' [1, 0, 2]
def ballot210 : ListBallot 3 := ListBallot.mk' [2, 1, 0]
def ballot012 : ListBallot 3 := ListBallot.mk' [0, 1, 2]

def ballots : Fin 13 → ListBallot 3
  | ⟨0, _⟩ => ballot021
  | ⟨1, _⟩ => ballot021
  | ⟨2, _⟩ => ballot021
  | ⟨3, _⟩ => ballot021
  | ⟨4, _⟩ => ballot021
  | ⟨5, _⟩ => ballot120
  | ⟨6, _⟩ => ballot120
  | ⟨7, _⟩ => ballot120
  | ⟨8, _⟩ => ballot102
  | ⟨9, _⟩ => ballot102
  | ⟨10, _⟩ => ballot102
  | ⟨11, _⟩ => ballot210
  | ⟨12, _⟩ => ballot012

noncomputable def profile : Profile (Fin 13) (Fin 3) :=
  profileOfListBallots ballots

local notation "scoreVec" => fun r => vetoScore 3 r

lemma lowestScoring_eq_singleton_one :
    lowestScoring profile scoreVec = ({1} : Finset (Fin 3)) := by
  decide

lemma marginList_1_0 :
    marginList (fun v => (ballots v).ranking) 1 0 = 1 := by
  decide

lemma marginList_1_2 :
    marginList (fun v => (ballots v).ranking) 1 2 = 1 := by
  decide

theorem condorcetWinner_one : CondorcetWinner profile (1 : Fin 3) := by
  rw [profile, CondorcetWinner_iff_marginList]
  intro d hne
  fin_cases d
  · have h : marginList (fun v => (ballots v).ranking) 1 0 = 1 := marginList_1_0
    simp [h]
  · cases hne rfl
  · have h : marginList (fun v => (ballots v).ranking) 1 2 = 1 := marginList_1_2
    simp [h]

noncomputable def profile' : Profile (Fin 13) {x : Fin 3 // x ≠ (1 : Fin 3)} :=
  restrictProfile profile (1 : Fin 3)

def cand0 : {x : Fin 3 // x ≠ (1 : Fin 3)} := ⟨0, by decide⟩
def cand2 : {x : Fin 3 // x ≠ (1 : Fin 3)} := ⟨2, by decide⟩

local notation "scoreVec2" => fun r => vetoScore 2 r

lemma lowestScoring_restrict_eq_singleton_cand2 :
    lowestScoring profile' scoreVec2 = ({cand2} : Finset {x : Fin 3 // x ≠ (1 : Fin 3)}) := by
  decide

lemma scoringEliminationAux_restrict_singleton :
    scoringEliminationAux vetoScore {x : {x : Fin 3 // x ≠ (1 : Fin 3)} // x ≠ cand2}
      (restrictProfile profile' cand2) =
      (Finset.univ : Finset {x : {x : Fin 3 // x ≠ (1 : Fin 3)} // x ≠ cand2}) := by
  simp [scoringEliminationAux]

lemma liftFinset_univ_restrict :
    liftFinset
      (Finset.univ : Finset {x : {x : Fin 3 // x ≠ (1 : Fin 3)} // x ≠ cand2}) =
        ({cand0} : Finset {x : Fin 3 // x ≠ (1 : Fin 3)}) := by
  decide

theorem coombs_profile_winner : coombs profile = ({0} : Finset (Fin 3)) := by
  classical
  have hcard : ¬ Fintype.card (Fin 3) ≤ 1 := by decide
  have haux :=
    scoringEliminationAux_eq_biUnion_of_not_card_le_one
      (score := vetoScore) (P := profile) (hcard := hcard)
  have haux' :
      scoringEliminationAux vetoScore (Fin 3) profile =
        ({1} : Finset (Fin 3)).biUnion
          (fun c => liftFinset (scoringEliminationAux vetoScore _ (restrictProfile profile c))) := by
    simpa [lowestScoring_eq_singleton_one] using haux
  have haux'' :
      scoringEliminationAux vetoScore (Fin 3) profile =
        liftFinset (scoringEliminationAux vetoScore _ (restrictProfile profile (1 : Fin 3))) := by
    simpa using haux'
  have hcard' : ¬ Fintype.card {x : Fin 3 // x ≠ (1 : Fin 3)} ≤ 1 := by
    have hcard'' : Fintype.card {x : Fin 3 // x ≠ (1 : Fin 3)} = 2 := by
      simp [card_subtype_ne_eq (1 : Fin 3)]
    omega
  have haux_restrict :=
    scoringEliminationAux_eq_biUnion_of_not_card_le_one
      (score := vetoScore) (P := profile') (hcard := hcard')
  have haux_restrict' :
      scoringEliminationAux vetoScore {x : Fin 3 // x ≠ (1 : Fin 3)} profile' =
        ({cand2} : Finset {x : Fin 3 // x ≠ (1 : Fin 3)}).biUnion
          (fun c => liftFinset (scoringEliminationAux vetoScore _ (restrictProfile profile' c))) := by
    simpa [lowestScoring_restrict_eq_singleton_cand2] using haux_restrict
  have haux_restrict'' :
      scoringEliminationAux vetoScore {x : Fin 3 // x ≠ (1 : Fin 3)} profile' =
        liftFinset (scoringEliminationAux vetoScore _ (restrictProfile profile' cand2)) := by
    simpa using haux_restrict'
  have hrec :
      scoringEliminationAux vetoScore {x : Fin 3 // x ≠ (1 : Fin 3)} profile' =
        ({cand0} : Finset {x : Fin 3 // x ≠ (1 : Fin 3)}) := by
    calc
      scoringEliminationAux vetoScore {x : Fin 3 // x ≠ (1 : Fin 3)} profile'
          = liftFinset (scoringEliminationAux vetoScore _ (restrictProfile profile' cand2)) := haux_restrict''
      _ = liftFinset
          (Finset.univ : Finset {x : {x : Fin 3 // x ≠ (1 : Fin 3)} // x ≠ cand2}) := by
            simp [scoringEliminationAux_restrict_singleton]
      _ = ({cand0} : Finset {x : Fin 3 // x ≠ (1 : Fin 3)}) := liftFinset_univ_restrict
  have hrec' :
      scoringEliminationAux vetoScore {x : Fin 3 // x ≠ (1 : Fin 3)}
        (restrictProfile profile (1 : Fin 3)) =
        ({cand0} : Finset {x : Fin 3 // x ≠ (1 : Fin 3)}) := by
    simpa [profile'] using hrec
  have hcoombs :
      coombs profile = scoringEliminationAux vetoScore (Fin 3) profile := by
    classical
    simpa [coombs, scoringEliminationRule] using
      (scoringEliminationAux_decidableEq_congr (score := vetoScore) (P := profile)
        (inst1 := Classical.decEq (Fin 3)) (inst2 := inferInstance))
  calc
    coombs profile
        = scoringEliminationAux vetoScore (Fin 3) profile := hcoombs
    _ = liftFinset
          (scoringEliminationAux vetoScore {x : Fin 3 // x ≠ (1 : Fin 3)}
            (restrictProfile profile (1 : Fin 3))) := by
            simpa [coombs, scoringEliminationRule] using haux''
    _ = liftFinset ({cand0} : Finset {x : Fin 3 // x ≠ (1 : Fin 3)}) := by
            simp [hrec']
    _ = ({0} : Finset (Fin 3)) := by
            simp [liftFinset, cand0]

theorem coombs_not_condorcet : ¬ CondorcetConsistency coombs := by
  intro hcond
  have hcw : CondorcetWinner profile (1 : Fin 3) := condorcetWinner_one
  have hsingle := hcond (P := profile) (c := (1 : Fin 3)) hcw
  have hne : (0 : Fin 3) ∈ coombs profile := by
    simp [coombs_profile_winner]
  have hcontra : False := by
    have hmem : (0 : Fin 3) ∈ ({1} : Finset (Fin 3)) := by
      have hne' := hne
      simp [hsingle] at hne'
    simp at hmem
  exact hcontra

end CoombsCondorcetCounterexample

end SocialChoice
