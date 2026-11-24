import Mathlib.Tactic
import Mathlib.Tactic.FinCases
import SocialChoice.Axioms.Implications
import SocialChoice.Axioms.Participation
import SocialChoice.ListBallot
import SocialChoice.ListBallotProfiles
import SocialChoice.Margin
import SocialChoice.Profile
import SocialChoice.Rules.ScoringElimination.Basic
import SocialChoice.Rules.ScoringElimination.Coombs.CondorcetLoser
import SocialChoice.Rules.ScoringElimination.Coombs.Defs
import SocialChoice.Rules.ScoringRules.Veto.Common

namespace SocialChoice

open Finset

/-!
# Coombs fails positive involvement

Counterexample with 3 candidates and 7 voters:

Full profile (7 voters):
1 voter : 0 > 2 > 1
2 voters: 1 > 0 > 2
1 voter : 1 > 2 > 0
1 voter : 2 > 0 > 1
2 voters: 2 > 1 > 0
Coombs selects {2}.

Remove the voter with ballot 1 > 2 > 0:
Coombs selects {0,1,2}.

Read backwards, this violates Positive Involvement for candidate 1.
-/

namespace CoombsPositiveInvolvementCounterexample

def ballot021 : ListBallot 3 := ListBallot.mk' [0, 2, 1]
def ballot102 : ListBallot 3 := ListBallot.mk' [1, 0, 2]
def ballot120 : ListBallot 3 := ListBallot.mk' [1, 2, 0]
def ballot201 : ListBallot 3 := ListBallot.mk' [2, 0, 1]
def ballot210 : ListBallot 3 := ListBallot.mk' [2, 1, 0]

def ballots7 : Fin 7 → ListBallot 3
  | ⟨0, _⟩ => ballot021
  | ⟨1, _⟩ => ballot102
  | ⟨2, _⟩ => ballot102
  | ⟨3, _⟩ => ballot120
  | ⟨4, _⟩ => ballot201
  | ⟨5, _⟩ => ballot210
  | ⟨6, _⟩ => ballot210

def voters6 : Finset (Fin 7) := {0, 1, 2, 4, 5, 6}
def voters7 : Finset (Fin 7) := insert (3 : Fin 7) voters6

lemma voters6_not_mem : (3 : Fin 7) ∉ voters6 := by
  simp [voters6]

noncomputable def fullProfile : Profile (Electorate (Fin 7) (Finset.univ)) (Fin 3) :=
  profileOfListBallots (fun v => ballots7 v.1)

noncomputable def profile6 : Profile (Electorate (Fin 7) voters6) (Fin 3) :=
  restrictElectorate fullProfile voters6 (by
    intro x hx; exact (Finset.mem_univ x))

noncomputable def profile7 : Profile (Electorate (Fin 7) voters7) (Fin 3) :=
  restrictElectorate fullProfile voters7 (by
    intro x hx; exact (Finset.mem_univ x))

lemma profile7_eq :
    profile7 = profileOfListBallots (fun v : Electorate (Fin 7) voters7 => ballots7 v.1) :=
  rfl

lemma profile6_eq :
    profile6 = profileOfListBallots (fun v : Electorate (Fin 7) voters6 => ballots7 v.1) :=
  rfl

lemma profiles_agree :
    ∀ v : Electorate (Fin 7) voters6,
      profile7.pref (liftVoter (u := (3 : Fin 7)) v) = profile6.pref v := by
  intro v
  simpa [profile6, profile7, voters7] using
    (restrictElectorate_agrees (Q := fullProfile) (S := voters6)
      (hS := by intro x hx; exact (Finset.mem_univ x))
      (u := (3 : Fin 7))
      (hSu := by intro x hx; exact (Finset.mem_univ x)) v)

lemma ballot120_top_1 : BallotTop ballot120.toLinearOrder (1 : Fin 3) := by
  intro x hx
  fin_cases x <;> simp [ballot120, ListBallot.lt_iff_idxOf, ListBallot.mk'] at hx ⊢

lemma newVoter_top_1 :
    BallotTop (profile7.pref (newVoter (u := (3 : Fin 7)) (V := voters6) voters6_not_mem))
      (1 : Fin 3) := by
  have hpref :
      profile7.pref (newVoter (u := (3 : Fin 7)) (V := voters6) voters6_not_mem) =
        ballot120.toLinearOrder :=
    rfl
  simpa [hpref] using ballot120_top_1

/-! ## First-round eliminations -/

local notation "scoreVec" => fun r => vetoScore 3 r

lemma lowestScoring_profile7_eq_singleton_0 :
    lowestScoring profile7 scoreVec = ({0} : Finset (Fin 3)) := by
  decide

lemma lowestScoring_profile6_eq_univ :
    lowestScoring profile6 scoreVec = (Finset.univ : Finset (Fin 3)) := by
  decide

/-! ## Pairwise margins -/

lemma margin_profile7_1_2 :
    margin profile7 (1 : Fin 3) (2 : Fin 3) = (-1 : Int) := by
  rw [profile7_eq, margin_profileOfListBallots]
  decide

lemma margin_profile6_1_0 :
    margin profile6 (1 : Fin 3) (0 : Fin 3) = (2 : Int) := by
  rw [profile6_eq, margin_profileOfListBallots]
  decide

/-! ## Coombs outcomes -/

def cand1_0 : {x : Fin 3 // x ≠ (0 : Fin 3)} := ⟨1, by decide⟩
def cand2_0 : {x : Fin 3 // x ≠ (0 : Fin 3)} := ⟨2, by decide⟩
def cand0_2 : {x : Fin 3 // x ≠ (2 : Fin 3)} := ⟨0, by decide⟩
def cand1_2 : {x : Fin 3 // x ≠ (2 : Fin 3)} := ⟨1, by decide⟩

lemma coombs_profile7_not_1 : (1 : Fin 3) ∉ coombs profile7 := by
  classical
  have hcard : ¬ Fintype.card (Fin 3) ≤ 1 := by decide
  have haux :=
    scoringEliminationAux_eq_biUnion_of_not_card_le_one
      (score := vetoScore) (P := profile7) (hcard := hcard)
  have haux' :
      scoringEliminationAux vetoScore (Fin 3) profile7 =
        ({0} : Finset (Fin 3)).biUnion
          (fun c => liftFinset (scoringEliminationAux vetoScore _ (restrictProfile profile7 c))) := by
    simpa [lowestScoring_profile7_eq_singleton_0] using haux
  have hcoombs :
      coombs profile7 = scoringEliminationAux vetoScore (Fin 3) profile7 := by
    classical
    simpa [coombs, scoringEliminationRule] using
      (scoringEliminationAux_decidableEq_congr (score := vetoScore) (P := profile7)
        (inst1 := Classical.decEq (Fin 3)) (inst2 := inferInstance))
  intro hmem
  have hmem' :
      (1 : Fin 3) ∈
        ({0} : Finset (Fin 3)).biUnion
          (fun c => liftFinset (scoringEliminationAux vetoScore _ (restrictProfile profile7 c))) := by
    simpa [hcoombs, haux'] using hmem
  rcases Finset.mem_biUnion.mp hmem' with ⟨c, hcL, hmem_c⟩
  have hc0 : c = (0 : Fin 3) := by
    simpa using (Finset.mem_singleton.mp hcL)
  subst hc0
  have hmem_c' :
      (1 : Fin 3) ∈
        liftFinset (scoringEliminationAux vetoScore _ (restrictProfile profile7 (0 : Fin 3))) := by
    simpa using hmem_c
  have hmem_sub_aux :
      cand1_0 ∈ scoringEliminationAux vetoScore _ (restrictProfile profile7 (0 : Fin 3)) := by
    rcases (mem_liftFinset_iff_subtype
      (s := scoringEliminationAux vetoScore _ (restrictProfile profile7 (0 : Fin 3)))
      (x := (1 : Fin 3))).1 hmem_c'
      with ⟨hx, hmem_sub⟩
    have hx' : (⟨1, hx⟩ : {x : Fin 3 // x ≠ (0 : Fin 3)}) = cand1_0 := by
      apply Subtype.ext
      rfl
    simpa [hx'] using hmem_sub
  have hcoombs_sub :
      coombs (restrictProfile profile7 (0 : Fin 3)) =
        scoringEliminationAux vetoScore _ (restrictProfile profile7 (0 : Fin 3)) := by
    classical
    simpa [coombs, scoringEliminationRule] using
      (scoringEliminationAux_decidableEq_congr (score := vetoScore)
        (P := restrictProfile profile7 (0 : Fin 3))
        (inst1 := Classical.decEq _) (inst2 := inferInstance))
  have hmem_sub :
      cand1_0 ∈ coombs (restrictProfile profile7 (0 : Fin 3)) := by
    simpa [hcoombs_sub] using hmem_sub_aux
  have hcard' : Fintype.card {x : Fin 3 // x ≠ (0 : Fin 3)} = 2 := by
    simp [card_subtype_ne_eq (0 : Fin 3)]
  have hiff :
      cand1_0 ∈ coombs (restrictProfile profile7 (0 : Fin 3)) ↔
        0 ≤ margin (restrictProfile profile7 (0 : Fin 3)) cand1_0 cand2_0 := by
    simpa [cand1_0, cand2_0] using
      (coombs_of_card_two (P := restrictProfile profile7 (0 : Fin 3)) (hcard := hcard')
        (a := cand1_0) (b := cand2_0) (hab := by decide))
  have hmargin :
      margin (restrictProfile profile7 (0 : Fin 3)) cand1_0 cand2_0 =
        margin profile7 (1 : Fin 3) (2 : Fin 3) := by
    simpa [cand1_0, cand2_0] using
      (margin_eq_margin_restrictProfile (P := profile7) (c := (0 : Fin 3))
        (a := cand1_0) (b := cand2_0)).symm
  have hmargin_val :
      margin (restrictProfile profile7 (0 : Fin 3)) cand1_0 cand2_0 = (-1 : Int) := by
    simpa [hmargin] using margin_profile7_1_2
  have hnot_le : ¬ (0 ≤ margin (restrictProfile profile7 (0 : Fin 3)) cand1_0 cand2_0) := by
    simp [hmargin_val]
  have hle : 0 ≤ margin (restrictProfile profile7 (0 : Fin 3)) cand1_0 cand2_0 :=
    (hiff.mp hmem_sub)
  exact (hnot_le hle)

lemma coombs_profile6_has_1 : (1 : Fin 3) ∈ coombs profile6 := by
  classical
  have hcard : ¬ Fintype.card (Fin 3) ≤ 1 := by decide
  have haux :=
    scoringEliminationAux_eq_biUnion_of_not_card_le_one
      (score := vetoScore) (P := profile6) (hcard := hcard)
  have haux' :
      scoringEliminationAux vetoScore (Fin 3) profile6 =
        (Finset.univ : Finset (Fin 3)).biUnion
          (fun c => liftFinset (scoringEliminationAux vetoScore _ (restrictProfile profile6 c))) := by
    simpa [lowestScoring_profile6_eq_univ] using haux
  have hcoombs :
      coombs profile6 = scoringEliminationAux vetoScore (Fin 3) profile6 := by
    classical
    simpa [coombs, scoringEliminationRule] using
      (scoringEliminationAux_decidableEq_congr (score := vetoScore) (P := profile6)
        (inst1 := Classical.decEq (Fin 3)) (inst2 := inferInstance))
  have hcard' : Fintype.card {x : Fin 3 // x ≠ (2 : Fin 3)} = 2 := by
    simp [card_subtype_ne_eq (2 : Fin 3)]
  have hiff :
      cand1_2 ∈ coombs (restrictProfile profile6 (2 : Fin 3)) ↔
        0 ≤ margin (restrictProfile profile6 (2 : Fin 3)) cand1_2 cand0_2 := by
    simpa [cand1_2, cand0_2] using
      (coombs_of_card_two (P := restrictProfile profile6 (2 : Fin 3)) (hcard := hcard')
        (a := cand1_2) (b := cand0_2) (hab := by decide))
  have hmargin :
      margin (restrictProfile profile6 (2 : Fin 3)) cand1_2 cand0_2 =
        margin profile6 (1 : Fin 3) (0 : Fin 3) := by
    simpa [cand1_2, cand0_2] using
      (margin_eq_margin_restrictProfile (P := profile6) (c := (2 : Fin 3))
        (a := cand1_2) (b := cand0_2)).symm
  have hmargin_val :
      margin (restrictProfile profile6 (2 : Fin 3)) cand1_2 cand0_2 = (2 : Int) := by
    simpa [hmargin] using margin_profile6_1_0
  have hle : 0 ≤ margin (restrictProfile profile6 (2 : Fin 3)) cand1_2 cand0_2 := by
    simp [hmargin_val]
  have hmem_sub : cand1_2 ∈ coombs (restrictProfile profile6 (2 : Fin 3)) := by
    exact (hiff.mpr hle)
  have hmem_lift :
      (1 : Fin 3) ∈
        liftFinset (scoringEliminationAux vetoScore _ (restrictProfile profile6 (2 : Fin 3))) := by
    have hcoombs_sub :
        coombs (restrictProfile profile6 (2 : Fin 3)) =
          scoringEliminationAux vetoScore _ (restrictProfile profile6 (2 : Fin 3)) := by
      classical
      simpa [coombs, scoringEliminationRule] using
        (scoringEliminationAux_decidableEq_congr (score := vetoScore)
          (P := restrictProfile profile6 (2 : Fin 3))
          (inst1 := Classical.decEq _) (inst2 := inferInstance))
    have hmem_sub' :
        cand1_2 ∈ scoringEliminationAux vetoScore _ (restrictProfile profile6 (2 : Fin 3)) := by
      simpa [hcoombs_sub] using hmem_sub
    exact (mem_liftFinset_iff_subtype
      (s := scoringEliminationAux vetoScore _ (restrictProfile profile6 (2 : Fin 3)))
      (x := (1 : Fin 3))).2 ⟨by decide, hmem_sub'⟩
  have hmem_union :
      (1 : Fin 3) ∈
        (Finset.univ : Finset (Fin 3)).biUnion
          (fun c => liftFinset (scoringEliminationAux vetoScore _ (restrictProfile profile6 c))) := by
    refine Finset.mem_biUnion.mpr ?_
    refine ⟨(2 : Fin 3), by simp, ?_⟩
    simpa [coombs, scoringEliminationRule] using hmem_lift
  simpa [hcoombs, haux'] using hmem_union

end CoombsPositiveInvolvementCounterexample

open CoombsPositiveInvolvementCounterexample

theorem coombs_not_positiveInvolvement : ¬ PositiveInvolvement coombs := by
  intro hpos
  have hmem : (1 : Fin 3) ∈ coombs profile6 := coombs_profile6_has_1
  have htop :
      BallotTop (profile7.pref (newVoter (u := (3 : Fin 7)) (V := voters6) voters6_not_mem))
        (1 : Fin 3) := newVoter_top_1
  have hmem' :
      (1 : Fin 3) ∈ coombs profile7 := by
    exact hpos (V := voters6) (u := (3 : Fin 7)) (hu := voters6_not_mem)
      (P := profile6) (Q := profile7) (c := (1 : Fin 3)) profiles_agree hmem htop
  exact coombs_profile7_not_1 hmem'

end SocialChoice
