import Mathlib.Tactic
import Mathlib.Tactic.FinCases
import SocialChoice.Axioms.Reversal
import SocialChoice.ListBallot
import SocialChoice.ListBallotProfiles
import SocialChoice.Rules.ScoringElimination.Basic
import SocialChoice.Rules.ScoringElimination.Baldwin.Defs
import SocialChoice.Rules.ScoringRules.Borda.Defs

namespace SocialChoice

open Finset

namespace BaldwinReversalCounterexample

def ballotBCA : ListBallot 3 := ListBallot.mk' [1, 2, 0]
def ballotCAB : ListBallot 3 := ListBallot.mk' [2, 0, 1]
def ballotABC : ListBallot 3 := ListBallot.mk' [0, 1, 2]

def ballots : Fin 5 → ListBallot 3
  | ⟨0, _⟩ => ballotBCA
  | ⟨1, _⟩ => ballotBCA
  | ⟨2, _⟩ => ballotCAB
  | ⟨3, _⟩ => ballotABC
  | ⟨4, _⟩ => ballotABC

noncomputable def profile : Profile (Fin 5) (Fin 3) :=
  profileOfListBallots ballots

abbrev cand0_2 : {x : Fin 3 // x ≠ (2 : Fin 3)} := ⟨0, by decide⟩
abbrev cand1_2 : {x : Fin 3 // x ≠ (2 : Fin 3)} := ⟨1, by decide⟩

abbrev cand0_1 : {x : Fin 3 // x ≠ (1 : Fin 3)} := ⟨0, by decide⟩
abbrev cand2_1 : {x : Fin 3 // x ≠ (1 : Fin 3)} := ⟨2, by decide⟩

private lemma baldwin_eq_aux {V A : Type} [Fintype V] [Fintype A] [DecidableEq A]
    (P : Profile V A) :
    baldwin P = scoringEliminationAux bordaScore A P := by
  classical
  simpa [baldwin, scoringEliminationRule] using
    (scoringEliminationAux_decidableEq_congr (score := bordaScore) (P := P)
      (inst1 := Classical.decEq A) (inst2 := inferInstance))

private lemma lowestScoring_profile_eq_singleton_2 :
    lowestScoring profile (fun r => bordaScore 3 r) = ({2} : Finset (Fin 3)) := by
  decide

private lemma lowestScoring_restrict_profile_eq_singleton_cand1 :
    lowestScoring (restrictProfile profile (2 : Fin 3)) (fun r => bordaScore 2 r) =
      ({cand1_2} : Finset {x : Fin 3 // x ≠ (2 : Fin 3)}) := by
  decide

private lemma lowestScoring_reverse_profile_eq_singleton_1 :
    lowestScoring (reverse_profile profile) (fun r => bordaScore 3 r) =
      ({1} : Finset (Fin 3)) := by
  decide

private lemma lowestScoring_reverse_restrict_eq_singleton_cand2 :
    lowestScoring (restrictProfile (reverse_profile profile) (1 : Fin 3)) (fun r => bordaScore 2 r) =
      ({cand2_1} : Finset {x : Fin 3 // x ≠ (1 : Fin 3)}) := by
  decide

lemma baldwin_profile_has_0 : (0 : Fin 3) ∈ baldwin profile := by
  classical
  have hbaldwin : baldwin profile = scoringEliminationAux bordaScore (Fin 3) profile :=
    baldwin_eq_aux (P := profile)
  have hcard : ¬ Fintype.card (Fin 3) ≤ 1 := by decide
  have haux :=
    scoringEliminationAux_eq_biUnion_of_not_card_le_one
      (score := bordaScore) (P := profile) (hcard := hcard)
  have haux' :
      scoringEliminationAux bordaScore (Fin 3) profile =
        ({2} : Finset (Fin 3)).biUnion
          (fun c => liftFinset (scoringEliminationAux bordaScore _
            (restrictProfile profile c))) := by
    simpa [lowestScoring_profile_eq_singleton_2] using haux
  have hcard' : ¬ Fintype.card {x : Fin 3 // x ≠ (2 : Fin 3)} ≤ 1 := by decide
  have haux_restrict :=
    scoringEliminationAux_eq_biUnion_of_not_card_le_one
      (score := bordaScore) (P := restrictProfile profile (2 : Fin 3)) (hcard := hcard')
  have haux_restrict' :
      scoringEliminationAux bordaScore _ (restrictProfile profile (2 : Fin 3)) =
        ({cand1_2} : Finset {x : Fin 3 // x ≠ (2 : Fin 3)}).biUnion
          (fun c => liftFinset (scoringEliminationAux bordaScore _
            (restrictProfile (restrictProfile profile (2 : Fin 3)) c))) := by
    simpa [lowestScoring_restrict_profile_eq_singleton_cand1] using haux_restrict
  have hbase :
      scoringEliminationAux bordaScore _
        (restrictProfile (restrictProfile profile (2 : Fin 3)) cand1_2) =
          (Finset.univ :
            Finset {x : {x : Fin 3 // x ≠ (2 : Fin 3)} // x ≠ cand1_2}) := by
    simp [scoringEliminationAux]
  have hmem_sub' :
      (⟨cand0_2, by decide⟩ :
          {x : {x : Fin 3 // x ≠ (2 : Fin 3)} // x ≠ cand1_2}) ∈
        scoringEliminationAux bordaScore _
          (restrictProfile (restrictProfile profile (2 : Fin 3)) cand1_2) := by
    simp [hbase]
  have hmem_lift :
      cand0_2 ∈
        liftFinset (scoringEliminationAux bordaScore _
          (restrictProfile (restrictProfile profile (2 : Fin 3)) cand1_2)) := by
    refine (mem_liftFinset_iff_subtype
      (s := scoringEliminationAux bordaScore _
        (restrictProfile (restrictProfile profile (2 : Fin 3)) cand1_2))
      (x := cand0_2)).2 ?_
    refine ⟨by decide, ?_⟩
    simpa using hmem_sub'
  have hmem_union :
      cand0_2 ∈
        ({cand1_2} : Finset {x : Fin 3 // x ≠ (2 : Fin 3)}).biUnion
          (fun c => liftFinset (scoringEliminationAux bordaScore _
            (restrictProfile (restrictProfile profile (2 : Fin 3)) c))) := by
    refine Finset.mem_biUnion.mpr ?_
    exact ⟨cand1_2, by simp, hmem_lift⟩
  have hmem_restrict :
      cand0_2 ∈ scoringEliminationAux bordaScore _
        (restrictProfile profile (2 : Fin 3)) := by
    simpa [haux_restrict'] using hmem_union
  have hmem_lift0 :
      (0 : Fin 3) ∈
        liftFinset (scoringEliminationAux bordaScore _
          (restrictProfile profile (2 : Fin 3))) := by
    refine (mem_liftFinset_iff_subtype
      (s := scoringEliminationAux bordaScore _ (restrictProfile profile (2 : Fin 3)))
      (x := (0 : Fin 3))).2 ?_
    refine ⟨by decide, ?_⟩
    have hx' :
        (⟨0, by decide⟩ : {x : Fin 3 // x ≠ (2 : Fin 3)}) = cand0_2 := by
      rfl
    simpa [hx'] using hmem_restrict
  have hmem_union0 :
      (0 : Fin 3) ∈
        ({2} : Finset (Fin 3)).biUnion
          (fun c => liftFinset (scoringEliminationAux bordaScore _
            (restrictProfile profile c))) := by
    refine Finset.mem_biUnion.mpr ?_
    exact ⟨(2 : Fin 3), by simp, hmem_lift0⟩
  simpa [hbaldwin, haux'] using hmem_union0

lemma baldwin_profile_not_2 : (2 : Fin 3) ∉ baldwin profile := by
  classical
  have hbaldwin : baldwin profile = scoringEliminationAux bordaScore (Fin 3) profile :=
    baldwin_eq_aux (P := profile)
  have hcard : ¬ Fintype.card (Fin 3) ≤ 1 := by decide
  have haux :=
    scoringEliminationAux_eq_biUnion_of_not_card_le_one
      (score := bordaScore) (P := profile) (hcard := hcard)
  have haux' :
      scoringEliminationAux bordaScore (Fin 3) profile =
        ({2} : Finset (Fin 3)).biUnion
          (fun c => liftFinset (scoringEliminationAux bordaScore _
            (restrictProfile profile c))) := by
    simpa [lowestScoring_profile_eq_singleton_2] using haux
  intro hmem
  have hmem' :
      (2 : Fin 3) ∈
        ({2} : Finset (Fin 3)).biUnion
          (fun c => liftFinset (scoringEliminationAux bordaScore _
            (restrictProfile profile c))) := by
    simpa [hbaldwin, haux'] using hmem
  rcases Finset.mem_biUnion.mp hmem' with ⟨c, hcL, hmem_c⟩
  have hc2 : c = (2 : Fin 3) := by
    simpa using (Finset.mem_singleton.mp hcL)
  subst hc2
  have hnot :
      (2 : Fin 3) ∉
        liftFinset (scoringEliminationAux bordaScore _
          (restrictProfile profile (2 : Fin 3))) := by
    exact not_mem_liftFinset_removed (c := (2 : Fin 3))
      (s := scoringEliminationAux bordaScore _ (restrictProfile profile (2 : Fin 3)))
  exact (hnot hmem_c).elim

lemma baldwin_profile_not_1 : (1 : Fin 3) ∉ baldwin profile := by
  classical
  have hbaldwin : baldwin profile = scoringEliminationAux bordaScore (Fin 3) profile :=
    baldwin_eq_aux (P := profile)
  have hcard : ¬ Fintype.card (Fin 3) ≤ 1 := by decide
  have haux :=
    scoringEliminationAux_eq_biUnion_of_not_card_le_one
      (score := bordaScore) (P := profile) (hcard := hcard)
  have haux' :
      scoringEliminationAux bordaScore (Fin 3) profile =
        ({2} : Finset (Fin 3)).biUnion
          (fun c => liftFinset (scoringEliminationAux bordaScore _
            (restrictProfile profile c))) := by
    simpa [lowestScoring_profile_eq_singleton_2] using haux
  intro hmem
  have hmem' :
      (1 : Fin 3) ∈
        ({2} : Finset (Fin 3)).biUnion
          (fun c => liftFinset (scoringEliminationAux bordaScore _
            (restrictProfile profile c))) := by
    simpa [hbaldwin, haux'] using hmem
  rcases Finset.mem_biUnion.mp hmem' with ⟨c, hcL, hmem_c⟩
  have hc2 : c = (2 : Fin 3) := by
    simpa using (Finset.mem_singleton.mp hcL)
  subst hc2
  have hmem_sub :
      cand1_2 ∈ scoringEliminationAux bordaScore _
        (restrictProfile profile (2 : Fin 3)) := by
    rcases (mem_liftFinset_iff_subtype
      (s := scoringEliminationAux bordaScore _ (restrictProfile profile (2 : Fin 3)))
      (x := (1 : Fin 3))).1 hmem_c with ⟨hx, hmem_sub⟩
    have hx' : (⟨1, hx⟩ : {x : Fin 3 // x ≠ (2 : Fin 3)}) = cand1_2 := by
      apply Subtype.ext
      rfl
    simpa [hx'] using hmem_sub
  have hcard' : ¬ Fintype.card {x : Fin 3 // x ≠ (2 : Fin 3)} ≤ 1 := by decide
  have haux_restrict :=
    scoringEliminationAux_eq_biUnion_of_not_card_le_one
      (score := bordaScore) (P := restrictProfile profile (2 : Fin 3)) (hcard := hcard')
  have haux_restrict' :
      scoringEliminationAux bordaScore _ (restrictProfile profile (2 : Fin 3)) =
        ({cand1_2} : Finset {x : Fin 3 // x ≠ (2 : Fin 3)}).biUnion
          (fun c => liftFinset (scoringEliminationAux bordaScore _
            (restrictProfile (restrictProfile profile (2 : Fin 3)) c))) := by
    simpa [lowestScoring_restrict_profile_eq_singleton_cand1] using haux_restrict
  have hmem_union :
      cand1_2 ∈
        ({cand1_2} : Finset {x : Fin 3 // x ≠ (2 : Fin 3)}).biUnion
          (fun c => liftFinset (scoringEliminationAux bordaScore _
            (restrictProfile (restrictProfile profile (2 : Fin 3)) c))) := by
    simpa [haux_restrict'] using hmem_sub
  rcases Finset.mem_biUnion.mp hmem_union with ⟨c, hcL, hmem_c'⟩
  have hc : c = cand1_2 := by
    simpa using (Finset.mem_singleton.mp hcL)
  subst hc
  have hnot :
      cand1_2 ∉
        liftFinset (scoringEliminationAux bordaScore _
          (restrictProfile (restrictProfile profile (2 : Fin 3)) cand1_2)) := by
    exact not_mem_liftFinset_removed (c := cand1_2)
      (s := scoringEliminationAux bordaScore _
        (restrictProfile (restrictProfile profile (2 : Fin 3)) cand1_2))
  exact (hnot hmem_c').elim

lemma baldwin_profile_eq_singleton :
    baldwin profile = ({0} : Finset (Fin 3)) := by
  classical
  ext x
  fin_cases x
  · simpa using baldwin_profile_has_0
  · constructor
    · intro hx
      exact (baldwin_profile_not_1 hx).elim
    · intro hx
      simp at hx
  · constructor
    · intro hx
      exact (baldwin_profile_not_2 hx).elim
    · intro hx
      simp at hx

lemma reverse_profile_has_0 : (0 : Fin 3) ∈ baldwin (reverse_profile profile) := by
  classical
  have hbaldwin :
      baldwin (reverse_profile profile) =
        scoringEliminationAux bordaScore (Fin 3) (reverse_profile profile) :=
    baldwin_eq_aux (P := reverse_profile profile)
  have hcard : ¬ Fintype.card (Fin 3) ≤ 1 := by decide
  have haux :=
    scoringEliminationAux_eq_biUnion_of_not_card_le_one
      (score := bordaScore) (P := reverse_profile profile) (hcard := hcard)
  have haux' :
      scoringEliminationAux bordaScore (Fin 3) (reverse_profile profile) =
        ({1} : Finset (Fin 3)).biUnion
          (fun c => liftFinset (scoringEliminationAux bordaScore _
            (restrictProfile (reverse_profile profile) c))) := by
    simpa [lowestScoring_reverse_profile_eq_singleton_1] using haux
  have hcard' : ¬ Fintype.card {x : Fin 3 // x ≠ (1 : Fin 3)} ≤ 1 := by decide
  have haux_restrict :=
    scoringEliminationAux_eq_biUnion_of_not_card_le_one
      (score := bordaScore)
      (P := restrictProfile (reverse_profile profile) (1 : Fin 3)) (hcard := hcard')
  have haux_restrict' :
      scoringEliminationAux bordaScore _
        (restrictProfile (reverse_profile profile) (1 : Fin 3)) =
        ({cand2_1} : Finset {x : Fin 3 // x ≠ (1 : Fin 3)}).biUnion
          (fun c => liftFinset (scoringEliminationAux bordaScore _
            (restrictProfile (restrictProfile (reverse_profile profile) (1 : Fin 3)) c))) := by
    simpa [lowestScoring_reverse_restrict_eq_singleton_cand2] using haux_restrict
  have hbase :
      scoringEliminationAux bordaScore _
        (restrictProfile (restrictProfile (reverse_profile profile) (1 : Fin 3)) cand2_1) =
          (Finset.univ :
            Finset {x : {x : Fin 3 // x ≠ (1 : Fin 3)} // x ≠ cand2_1}) := by
    simp [scoringEliminationAux]
  have hmem_sub' :
      (⟨cand0_1, by decide⟩ :
          {x : {x : Fin 3 // x ≠ (1 : Fin 3)} // x ≠ cand2_1}) ∈
        scoringEliminationAux bordaScore _
          (restrictProfile (restrictProfile (reverse_profile profile) (1 : Fin 3)) cand2_1) := by
    simp [hbase]
  have hmem_lift :
      cand0_1 ∈
        liftFinset (scoringEliminationAux bordaScore _
          (restrictProfile (restrictProfile (reverse_profile profile) (1 : Fin 3)) cand2_1)) := by
    refine (mem_liftFinset_iff_subtype
      (s := scoringEliminationAux bordaScore _
        (restrictProfile (restrictProfile (reverse_profile profile) (1 : Fin 3)) cand2_1))
      (x := cand0_1)).2 ?_
    refine ⟨by decide, ?_⟩
    simpa using hmem_sub'
  have hmem_union :
      cand0_1 ∈
        ({cand2_1} : Finset {x : Fin 3 // x ≠ (1 : Fin 3)}).biUnion
          (fun c => liftFinset (scoringEliminationAux bordaScore _
            (restrictProfile (restrictProfile (reverse_profile profile) (1 : Fin 3)) c))) := by
    refine Finset.mem_biUnion.mpr ?_
    exact ⟨cand2_1, by simp, hmem_lift⟩
  have hmem_restrict :
      cand0_1 ∈ scoringEliminationAux bordaScore _
        (restrictProfile (reverse_profile profile) (1 : Fin 3)) := by
    simpa [haux_restrict'] using hmem_union
  have hmem_lift0 :
      (0 : Fin 3) ∈
        liftFinset (scoringEliminationAux bordaScore _
          (restrictProfile (reverse_profile profile) (1 : Fin 3))) := by
    refine (mem_liftFinset_iff_subtype
      (s := scoringEliminationAux bordaScore _
        (restrictProfile (reverse_profile profile) (1 : Fin 3)))
      (x := (0 : Fin 3))).2 ?_
    refine ⟨by decide, ?_⟩
    have hx' :
        (⟨0, by decide⟩ : {x : Fin 3 // x ≠ (1 : Fin 3)}) = cand0_1 := by
      rfl
    simpa [hx'] using hmem_restrict
  have hmem_union0 :
      (0 : Fin 3) ∈
        ({1} : Finset (Fin 3)).biUnion
          (fun c => liftFinset (scoringEliminationAux bordaScore _
            (restrictProfile (reverse_profile profile) c))) := by
    refine Finset.mem_biUnion.mpr ?_
    exact ⟨(1 : Fin 3), by simp, hmem_lift0⟩
  simpa [hbaldwin, haux'] using hmem_union0

end BaldwinReversalCounterexample

open BaldwinReversalCounterexample

theorem baldwin_not_singletonReversalSymmetry :
    ¬ SingletonReversalSymmetry baldwin := by
  intro h
  have hne : ∃ y : Fin 3, (0 : Fin 3) ≠ y := by
    exact ⟨1, by decide⟩
  have hsingle : baldwin profile = ({0} : Finset (Fin 3)) :=
    baldwin_profile_eq_singleton
  have hnot :
      (0 : Fin 3) ∉ baldwin (reverse_profile profile) :=
    h (P := profile) (x := (0 : Fin 3)) hne hsingle
  have hmem : (0 : Fin 3) ∈ baldwin (reverse_profile profile) :=
    reverse_profile_has_0
  exact hnot hmem

end SocialChoice
