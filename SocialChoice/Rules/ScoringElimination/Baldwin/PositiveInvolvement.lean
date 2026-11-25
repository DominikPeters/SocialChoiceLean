import Mathlib.Tactic
import Mathlib.Tactic.FinCases
import SocialChoice.Axioms.Implications
import SocialChoice.Axioms.Participation
import SocialChoice.ListBallot
import SocialChoice.ListBallotProfiles
import SocialChoice.Margin
import SocialChoice.Profile
import SocialChoice.Rules.ScoringElimination.Basic
import SocialChoice.Rules.ScoringElimination.Baldwin.Defs
import SocialChoice.Rules.ScoringRules.Plurality.Defs
import SocialChoice.Rules.ScoringRules.Veto.Common

namespace SocialChoice

open Finset

/-!
# Baldwin fails positive involvement

Counterexample with 3 candidates and 7 voters:

Full profile (7 voters):
2 voters: 0 > 2 > 1
2 voters: 1 > 0 > 2
1 voter : 2 > 0 > 1
2 voters: 2 > 1 > 0
Baldwin selects {0}.

Remove the voter with ballot 2 > 0 > 1:
Baldwin selects {0,1,2}.

Read backwards, this violates Positive Involvement for candidate 2.
-/

namespace BaldwinPositiveInvolvementCounterexample

-- Ballots

def ballot021 : ListBallot 3 := ListBallot.mk' [0, 2, 1]
def ballot102 : ListBallot 3 := ListBallot.mk' [1, 0, 2]
def ballot201 : ListBallot 3 := ListBallot.mk' [2, 0, 1]
def ballot210 : ListBallot 3 := ListBallot.mk' [2, 1, 0]

-- 7 voters: two 021, two 102, one 201 (to be removed), two 210

def ballots7 : Fin 7 → ListBallot 3
  | ⟨0, _⟩ => ballot021
  | ⟨1, _⟩ => ballot021
  | ⟨2, _⟩ => ballot102
  | ⟨3, _⟩ => ballot201
  | ⟨4, _⟩ => ballot102
  | ⟨5, _⟩ => ballot210
  | ⟨6, _⟩ => ballot210

-- Electorates: `voters6` omits voter 3 (the 201 ballot), `voters7` adds it back

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

lemma profiles_agree :
    ∀ v : Electorate (Fin 7) voters6,
      profile7.pref (liftVoter (u := (3 : Fin 7)) v) = profile6.pref v := by
  intro v
  simpa [profile6, profile7, voters7] using
    (restrictElectorate_agrees (Q := fullProfile) (S := voters6)
      (hS := by intro x hx; exact (Finset.mem_univ x))
      (u := (3 : Fin 7))
      (hSu := by intro x hx; exact (Finset.mem_univ x)) v)

lemma ballot201_top_2 : BallotTop ballot201.toLinearOrder (2 : Fin 3) := by
  intro x hx
  fin_cases x <;> simp [ballot201, ListBallot.lt_iff_idxOf, ListBallot.mk'] at hx ⊢

lemma newVoter_top_2 :
    BallotTop (profile7.pref (newVoter (u := (3 : Fin 7)) (V := voters6) voters6_not_mem))
      (2 : Fin 3) := by
  have hpref :
      profile7.pref (newVoter (u := (3 : Fin 7)) (V := voters6) voters6_not_mem) =
        ballot201.toLinearOrder :=
    rfl
  simpa [hpref] using ballot201_top_2

/-! ## Lowest-scoring candidates -/

def cand0_1 : {x : Fin 3 // x ≠ (1 : Fin 3)} := ⟨0, by decide⟩
def cand2_1 : {x : Fin 3 // x ≠ (1 : Fin 3)} := ⟨2, by decide⟩

def cand1_0 : {x : Fin 3 // x ≠ (0 : Fin 3)} := ⟨1, by decide⟩
def cand2_0 : {x : Fin 3 // x ≠ (0 : Fin 3)} := ⟨2, by decide⟩

lemma lowestScoring_profile7_eq_singleton_1 :
    lowestScoring profile7 (fun r => bordaScore 3 r) = ({1} : Finset (Fin 3)) := by
  decide

lemma lowestScoring_profile6_eq_univ :
    lowestScoring profile6 (fun r => bordaScore 3 r) = (Finset.univ : Finset (Fin 3)) := by
  decide

lemma lowestScoring_restrict_profile7_eq_singleton_cand2 :
    lowestScoring (restrictProfile profile7 (1 : Fin 3)) (fun r => bordaScore 2 r) =
      ({cand2_1} : Finset {x : Fin 3 // x ≠ (1 : Fin 3)}) := by
  decide

lemma lowestScoring_restrict_profile6_eq_singleton_cand1 :
    lowestScoring (restrictProfile profile6 (0 : Fin 3)) (fun r => bordaScore 2 r) =
      ({cand1_0} : Finset {x : Fin 3 // x ≠ (0 : Fin 3)}) := by
  decide

/-! ## Baldwin outcomes -/

lemma baldwin_profile7_not_2 : (2 : Fin 3) ∉ baldwin profile7 := by
  classical
  have hcard : ¬ Fintype.card (Fin 3) ≤ 1 := by decide
  have haux :=
    scoringEliminationAux_eq_biUnion_of_not_card_le_one
      (score := bordaScore) (P := profile7) (hcard := hcard)
  have haux' :
      scoringEliminationAux bordaScore (Fin 3) profile7 =
        ({1} : Finset (Fin 3)).biUnion
          (fun c => liftFinset (scoringEliminationAux bordaScore _ (restrictProfile profile7 c))) := by
    simpa [lowestScoring_profile7_eq_singleton_1] using haux
  have hbaldwin :
      baldwin profile7 = scoringEliminationAux bordaScore (Fin 3) profile7 := by
    classical
    simpa [baldwin, scoringEliminationRule] using
      (scoringEliminationAux_decidableEq_congr (score := bordaScore) (P := profile7)
        (inst1 := Classical.decEq (Fin 3)) (inst2 := inferInstance))
  intro hmem
  have hmem' :
      (2 : Fin 3) ∈
        ({1} : Finset (Fin 3)).biUnion
          (fun c => liftFinset (scoringEliminationAux bordaScore _ (restrictProfile profile7 c))) := by
    simpa [hbaldwin, haux'] using hmem
  rcases Finset.mem_biUnion.mp hmem' with ⟨c, hcL, hmem_c⟩
  have hc1 : c = (1 : Fin 3) := by
    simpa using (Finset.mem_singleton.mp hcL)
  subst hc1
  have hmem_c' :
      (2 : Fin 3) ∈
        liftFinset (scoringEliminationAux bordaScore _ (restrictProfile profile7 (1 : Fin 3))) := by
    simpa using hmem_c
  have hmem_sub :
      cand2_1 ∈ scoringEliminationAux bordaScore _ (restrictProfile profile7 (1 : Fin 3)) := by
    rcases (mem_liftFinset_iff_subtype
      (s := scoringEliminationAux bordaScore _ (restrictProfile profile7 (1 : Fin 3)))
      (x := (2 : Fin 3))).1 hmem_c'
      with ⟨hx, hmem_sub⟩
    have hx' : (⟨2, hx⟩ : {x : Fin 3 // x ≠ (1 : Fin 3)}) = cand2_1 := by
      apply Subtype.ext
      rfl
    simpa [hx'] using hmem_sub
  have hcard' : ¬ Fintype.card {x : Fin 3 // x ≠ (1 : Fin 3)} ≤ 1 := by decide
  have haux_restrict :=
    scoringEliminationAux_eq_biUnion_of_not_card_le_one
      (score := bordaScore) (P := restrictProfile profile7 (1 : Fin 3)) (hcard := hcard')
  have haux_restrict' :
      scoringEliminationAux bordaScore _ (restrictProfile profile7 (1 : Fin 3)) =
        ({cand2_1} : Finset {x : Fin 3 // x ≠ (1 : Fin 3)}).biUnion
          (fun c => liftFinset (scoringEliminationAux bordaScore _
            (restrictProfile (restrictProfile profile7 (1 : Fin 3)) c))) := by
    simpa [lowestScoring_restrict_profile7_eq_singleton_cand2] using haux_restrict
  have hmem_union :
      cand2_1 ∈
        ({cand2_1} : Finset {x : Fin 3 // x ≠ (1 : Fin 3)}).biUnion
          (fun c => liftFinset (scoringEliminationAux bordaScore _
            (restrictProfile (restrictProfile profile7 (1 : Fin 3)) c))) := by
    simpa [haux_restrict'] using hmem_sub
  rcases Finset.mem_biUnion.mp hmem_union with ⟨c, hcL, hmem_c''⟩
  have hc : c = cand2_1 := by
    simpa using (Finset.mem_singleton.mp hcL)
  subst hc
  have hnot :
      cand2_1 ∉
        liftFinset (scoringEliminationAux bordaScore _
          (restrictProfile (restrictProfile profile7 (1 : Fin 3)) cand2_1)) := by
    exact not_mem_liftFinset_removed (c := cand2_1)
      (s := scoringEliminationAux bordaScore _
        (restrictProfile (restrictProfile profile7 (1 : Fin 3)) cand2_1))
  exact (hnot hmem_c'').elim

lemma baldwin_profile6_has_2 : (2 : Fin 3) ∈ baldwin profile6 := by
  classical
  have hcard : ¬ Fintype.card (Fin 3) ≤ 1 := by decide
  have haux :=
    scoringEliminationAux_eq_biUnion_of_not_card_le_one
      (score := bordaScore) (P := profile6) (hcard := hcard)
  have haux' :
      scoringEliminationAux bordaScore (Fin 3) profile6 =
        (Finset.univ : Finset (Fin 3)).biUnion
          (fun c => liftFinset (scoringEliminationAux bordaScore _ (restrictProfile profile6 c))) := by
    simpa [lowestScoring_profile6_eq_univ] using haux
  have hbaldwin :
      baldwin profile6 = scoringEliminationAux bordaScore (Fin 3) profile6 := by
    classical
    simpa [baldwin, scoringEliminationRule] using
      (scoringEliminationAux_decidableEq_congr (score := bordaScore) (P := profile6)
        (inst1 := Classical.decEq (Fin 3)) (inst2 := inferInstance))
  have hmem_sub :
      cand2_0 ∈ scoringEliminationAux bordaScore _ (restrictProfile profile6 (0 : Fin 3)) := by
    -- In the restricted profile, cand1_0 is lowest, so winners come from removing it
    have hcard' : ¬ Fintype.card {x : Fin 3 // x ≠ (0 : Fin 3)} ≤ 1 := by decide
    have haux_restrict :=
      scoringEliminationAux_eq_biUnion_of_not_card_le_one
        (score := bordaScore) (P := restrictProfile profile6 (0 : Fin 3)) (hcard := hcard')
    have haux_restrict' :
        scoringEliminationAux bordaScore _ (restrictProfile profile6 (0 : Fin 3)) =
          ({cand1_0} : Finset {x : Fin 3 // x ≠ (0 : Fin 3)}).biUnion
            (fun c => liftFinset (scoringEliminationAux bordaScore _
              (restrictProfile (restrictProfile profile6 (0 : Fin 3)) c))) := by
      simpa [lowestScoring_restrict_profile6_eq_singleton_cand1] using haux_restrict
    have hmem_lift :
        cand2_0 ∈
          liftFinset (scoringEliminationAux bordaScore _
            (restrictProfile (restrictProfile profile6 (0 : Fin 3)) cand1_0)) := by
      -- Base case: only cand2_0 remains
      have hbase :
          scoringEliminationAux bordaScore _
            (restrictProfile (restrictProfile profile6 (0 : Fin 3)) cand1_0) =
              (Finset.univ : Finset {x : {x : Fin 3 // x ≠ (0 : Fin 3)} // x ≠ cand1_0}) := by
        simp [scoringEliminationAux]
      have hmem_sub' :
          (⟨cand2_0, by decide⟩ :
              {x : {x : Fin 3 // x ≠ (0 : Fin 3)} // x ≠ cand1_0}) ∈
            scoringEliminationAux bordaScore _
              (restrictProfile (restrictProfile profile6 (0 : Fin 3)) cand1_0) := by
        simp [hbase]
      exact (mem_liftFinset_iff_subtype
        (s := scoringEliminationAux bordaScore _
          (restrictProfile (restrictProfile profile6 (0 : Fin 3)) cand1_0))
        (x := (cand2_0 : {x : Fin 3 // x ≠ (0 : Fin 3)}))).2 ⟨by decide, hmem_sub'⟩
    have hmem_union :
        cand2_0 ∈
          ({cand1_0} : Finset {x : Fin 3 // x ≠ (0 : Fin 3)}).biUnion
            (fun c => liftFinset (scoringEliminationAux bordaScore _
              (restrictProfile (restrictProfile profile6 (0 : Fin 3)) c))) := by
      refine Finset.mem_biUnion.mpr ?_
      refine ⟨cand1_0, by simp, hmem_lift⟩
    simpa [haux_restrict'] using hmem_union
  have hmem_lift :
      (2 : Fin 3) ∈
        liftFinset (scoringEliminationAux bordaScore _ (restrictProfile profile6 (0 : Fin 3))) := by
    exact (mem_liftFinset_iff_subtype
      (s := scoringEliminationAux bordaScore _ (restrictProfile profile6 (0 : Fin 3)))
      (x := (2 : Fin 3))).2 ⟨by decide, hmem_sub⟩
  have hmem_union :
      (2 : Fin 3) ∈
        (Finset.univ : Finset (Fin 3)).biUnion
          (fun c => liftFinset (scoringEliminationAux bordaScore _ (restrictProfile profile6 c))) := by
    refine Finset.mem_biUnion.mpr ?_
    refine ⟨(0 : Fin 3), by simp, ?_⟩
    simpa using hmem_lift
  simpa [hbaldwin, haux'] using hmem_union

end BaldwinPositiveInvolvementCounterexample

open BaldwinPositiveInvolvementCounterexample

theorem baldwin_not_positiveInvolvement : ¬ PositiveInvolvement baldwin := by
  intro hpos
  have hmem : (2 : Fin 3) ∈ baldwin profile6 := baldwin_profile6_has_2
  have htop :
      BallotTop (profile7.pref (newVoter (u := (3 : Fin 7)) (V := voters6) voters6_not_mem))
        (2 : Fin 3) := newVoter_top_2
  have hmem' :
      (2 : Fin 3) ∈ baldwin profile7 := by
    exact hpos (V := voters6) (u := (3 : Fin 7)) (hu := voters6_not_mem)
      (P := profile6) (Q := profile7) (c := (2 : Fin 3)) profiles_agree hmem htop
  exact baldwin_profile7_not_2 hmem'

end SocialChoice
