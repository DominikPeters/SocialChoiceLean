import Mathlib.Tactic
import Mathlib.Tactic.FinCases
import SocialChoice.Axioms.Reversal
import SocialChoice.ListBallot
import SocialChoice.Rules.ScoringElimination.Basic
import SocialChoice.Rules.ScoringElimination.Coombs.Defs
import SocialChoice.Rules.ScoringRules.Veto.Defs

namespace SocialChoice

open Finset

namespace CoombsReversalCounterexample

def ballot021 : ListBallot 3 := ListBallot.mk' [0, 2, 1]
def ballot102 : ListBallot 3 := ListBallot.mk' [1, 0, 2]
def ballot120 : ListBallot 3 := ListBallot.mk' [1, 2, 0]
def ballot210 : ListBallot 3 := ListBallot.mk' [2, 1, 0]

def ballots : Fin 6 → ListBallot 3
  | ⟨0, _⟩ => ballot021
  | ⟨1, _⟩ => ballot021
  | ⟨2, _⟩ => ballot102
  | ⟨3, _⟩ => ballot120
  | ⟨4, _⟩ => ballot210
  | ⟨5, _⟩ => ballot210

noncomputable def profile : Profile (Fin 6) (Fin 3) :=
  profileOfListBallots ballots

abbrev cand1_0 : {x : Fin 3 // x ≠ (0 : Fin 3)} := ⟨1, by decide⟩
abbrev cand2_0 : {x : Fin 3 // x ≠ (0 : Fin 3)} := ⟨2, by decide⟩

abbrev cand0_1 : {x : Fin 3 // x ≠ (1 : Fin 3)} := ⟨0, by decide⟩
abbrev cand2_1 : {x : Fin 3 // x ≠ (1 : Fin 3)} := ⟨2, by decide⟩

private lemma coombs_eq_aux {V A : Type} [Fintype V] [Fintype A] [DecidableEq A]
    (P : Profile V A) :
    coombs P = scoringEliminationAux vetoScore A P := by
  classical
  simpa [coombs, scoringEliminationRule] using
    (scoringEliminationAux_decidableEq_congr (score := vetoScore) (P := P)
      (inst1 := Classical.decEq A) (inst2 := inferInstance))

private lemma lowestScoring_profile_eq_singleton_0 :
    lowestScoring profile (fun r => vetoScore 3 r) = ({0} : Finset (Fin 3)) := by
  decide

private lemma lowestScoring_restrict_profile_eq_singleton_cand1 :
    lowestScoring (restrictProfile profile (0 : Fin 3)) (fun r => vetoScore 2 r) =
      ({cand1_0} : Finset {x : Fin 3 // x ≠ (0 : Fin 3)}) := by
  decide

private lemma lowestScoring_reverse_profile_eq_univ :
    lowestScoring (reverse_profile profile) (fun r => vetoScore 3 r) =
      (Finset.univ : Finset (Fin 3)) := by
  decide

private lemma lowestScoring_reverse_restrict_eq_univ :
    lowestScoring (restrictProfile (reverse_profile profile) (1 : Fin 3))
      (fun r => vetoScore 2 r) =
      (Finset.univ : Finset {x : Fin 3 // x ≠ (1 : Fin 3)}) := by
  decide

lemma coombs_profile_has_2 : (2 : Fin 3) ∈ coombs profile := by
  classical
  have hcoombs : coombs profile = scoringEliminationAux vetoScore (Fin 3) profile :=
    coombs_eq_aux (P := profile)
  have hcard : ¬ Fintype.card (Fin 3) ≤ 1 := by decide
  have haux :=
    scoringEliminationAux_eq_biUnion_of_not_card_le_one
      (score := vetoScore) (P := profile) (hcard := hcard)
  have haux' :
      scoringEliminationAux vetoScore (Fin 3) profile =
        ({0} : Finset (Fin 3)).biUnion
          (fun c => liftFinset (scoringEliminationAux vetoScore _
            (restrictProfile profile c))) := by
    simpa [lowestScoring_profile_eq_singleton_0] using haux
  have hmem_sub :
      cand2_0 ∈ scoringEliminationAux vetoScore _ (restrictProfile profile (0 : Fin 3)) := by
    have hcard' : ¬ Fintype.card {x : Fin 3 // x ≠ (0 : Fin 3)} ≤ 1 := by decide
    have haux_restrict :=
      scoringEliminationAux_eq_biUnion_of_not_card_le_one
        (score := vetoScore) (P := restrictProfile profile (0 : Fin 3)) (hcard := hcard')
    have haux_restrict' :
        scoringEliminationAux vetoScore _ (restrictProfile profile (0 : Fin 3)) =
          ({cand1_0} : Finset {x : Fin 3 // x ≠ (0 : Fin 3)}).biUnion
            (fun c => liftFinset (scoringEliminationAux vetoScore _
              (restrictProfile (restrictProfile profile (0 : Fin 3)) c))) := by
      simpa [lowestScoring_restrict_profile_eq_singleton_cand1] using haux_restrict
    have hbase :
        scoringEliminationAux vetoScore _
          (restrictProfile (restrictProfile profile (0 : Fin 3)) cand1_0) =
            (Finset.univ :
              Finset {x : {x : Fin 3 // x ≠ (0 : Fin 3)} // x ≠ cand1_0}) := by
      simp [scoringEliminationAux]
    have hmem_sub' :
        (⟨cand2_0, by decide⟩ :
            {x : {x : Fin 3 // x ≠ (0 : Fin 3)} // x ≠ cand1_0}) ∈
          scoringEliminationAux vetoScore _
            (restrictProfile (restrictProfile profile (0 : Fin 3)) cand1_0) := by
      simp [hbase]
    have hmem_lift :
        cand2_0 ∈
          liftFinset (scoringEliminationAux vetoScore _
            (restrictProfile (restrictProfile profile (0 : Fin 3)) cand1_0)) := by
      refine (mem_liftFinset_iff_subtype
        (s := scoringEliminationAux vetoScore _
          (restrictProfile (restrictProfile profile (0 : Fin 3)) cand1_0))
        (x := cand2_0)).2 ?_
      refine ⟨by decide, ?_⟩
      simpa using hmem_sub'
    have hmem_union :
        cand2_0 ∈
          ({cand1_0} : Finset {x : Fin 3 // x ≠ (0 : Fin 3)}).biUnion
            (fun c => liftFinset (scoringEliminationAux vetoScore _
              (restrictProfile (restrictProfile profile (0 : Fin 3)) c))) := by
      refine Finset.mem_biUnion.mpr ?_
      exact ⟨cand1_0, by simp, hmem_lift⟩
    simpa [haux_restrict'] using hmem_union
  have hmem_lift0 :
      (2 : Fin 3) ∈
        liftFinset (scoringEliminationAux vetoScore _
          (restrictProfile profile (0 : Fin 3))) := by
    refine (mem_liftFinset_iff_subtype
      (s := scoringEliminationAux vetoScore _ (restrictProfile profile (0 : Fin 3)))
      (x := (2 : Fin 3))).2 ?_
    refine ⟨by decide, ?_⟩
    have hx' :
        (⟨2, by decide⟩ : {x : Fin 3 // x ≠ (0 : Fin 3)}) = cand2_0 := by
      rfl
    simpa [hx'] using hmem_sub
  have hmem_union0 :
      (2 : Fin 3) ∈
        ({0} : Finset (Fin 3)).biUnion
          (fun c => liftFinset (scoringEliminationAux vetoScore _
            (restrictProfile profile c))) := by
    refine Finset.mem_biUnion.mpr ?_
    exact ⟨(0 : Fin 3), by simp, hmem_lift0⟩
  simpa [hcoombs, haux'] using hmem_union0

lemma coombs_profile_not_0 : (0 : Fin 3) ∉ coombs profile := by
  classical
  have hcoombs : coombs profile = scoringEliminationAux vetoScore (Fin 3) profile :=
    coombs_eq_aux (P := profile)
  have hcard : ¬ Fintype.card (Fin 3) ≤ 1 := by decide
  have haux :=
    scoringEliminationAux_eq_biUnion_of_not_card_le_one
      (score := vetoScore) (P := profile) (hcard := hcard)
  have haux' :
      scoringEliminationAux vetoScore (Fin 3) profile =
        ({0} : Finset (Fin 3)).biUnion
          (fun c => liftFinset (scoringEliminationAux vetoScore _
            (restrictProfile profile c))) := by
    simpa [lowestScoring_profile_eq_singleton_0] using haux
  intro hmem
  have hmem' :
      (0 : Fin 3) ∈
        ({0} : Finset (Fin 3)).biUnion
          (fun c => liftFinset (scoringEliminationAux vetoScore _
            (restrictProfile profile c))) := by
    simpa [hcoombs, haux'] using hmem
  rcases Finset.mem_biUnion.mp hmem' with ⟨c, hcL, hmem_c⟩
  have hc0 : c = (0 : Fin 3) := by
    simpa using (Finset.mem_singleton.mp hcL)
  subst hc0
  have hnot :
      (0 : Fin 3) ∉
        liftFinset (scoringEliminationAux vetoScore _
          (restrictProfile profile (0 : Fin 3))) := by
    exact not_mem_liftFinset_removed (c := (0 : Fin 3))
      (s := scoringEliminationAux vetoScore _ (restrictProfile profile (0 : Fin 3)))
  exact (hnot hmem_c).elim

lemma coombs_profile_not_1 : (1 : Fin 3) ∉ coombs profile := by
  classical
  have hcoombs : coombs profile = scoringEliminationAux vetoScore (Fin 3) profile :=
    coombs_eq_aux (P := profile)
  have hcard : ¬ Fintype.card (Fin 3) ≤ 1 := by decide
  have haux :=
    scoringEliminationAux_eq_biUnion_of_not_card_le_one
      (score := vetoScore) (P := profile) (hcard := hcard)
  have haux' :
      scoringEliminationAux vetoScore (Fin 3) profile =
        ({0} : Finset (Fin 3)).biUnion
          (fun c => liftFinset (scoringEliminationAux vetoScore _
            (restrictProfile profile c))) := by
    simpa [lowestScoring_profile_eq_singleton_0] using haux
  intro hmem
  have hmem' :
      (1 : Fin 3) ∈
        ({0} : Finset (Fin 3)).biUnion
          (fun c => liftFinset (scoringEliminationAux vetoScore _
            (restrictProfile profile c))) := by
    simpa [hcoombs, haux'] using hmem
  rcases Finset.mem_biUnion.mp hmem' with ⟨c, hcL, hmem_c⟩
  have hc0 : c = (0 : Fin 3) := by
    simpa using (Finset.mem_singleton.mp hcL)
  subst hc0
  have hmem_sub :
      cand1_0 ∈ scoringEliminationAux vetoScore _ (restrictProfile profile (0 : Fin 3)) := by
    rcases (mem_liftFinset_iff_subtype
      (s := scoringEliminationAux vetoScore _ (restrictProfile profile (0 : Fin 3)))
      (x := (1 : Fin 3))).1 hmem_c with ⟨hx, hmem_sub⟩
    have hx' : (⟨1, hx⟩ : {x : Fin 3 // x ≠ (0 : Fin 3)}) = cand1_0 := by
      apply Subtype.ext
      rfl
    simpa [hx'] using hmem_sub
  have hcard' : ¬ Fintype.card {x : Fin 3 // x ≠ (0 : Fin 3)} ≤ 1 := by decide
  have haux_restrict :=
    scoringEliminationAux_eq_biUnion_of_not_card_le_one
      (score := vetoScore) (P := restrictProfile profile (0 : Fin 3)) (hcard := hcard')
  have haux_restrict' :
      scoringEliminationAux vetoScore _ (restrictProfile profile (0 : Fin 3)) =
        ({cand1_0} : Finset {x : Fin 3 // x ≠ (0 : Fin 3)}).biUnion
          (fun c => liftFinset (scoringEliminationAux vetoScore _
            (restrictProfile (restrictProfile profile (0 : Fin 3)) c))) := by
    simpa [lowestScoring_restrict_profile_eq_singleton_cand1] using haux_restrict
  have hmem_union :
      cand1_0 ∈
        ({cand1_0} : Finset {x : Fin 3 // x ≠ (0 : Fin 3)}).biUnion
          (fun c => liftFinset (scoringEliminationAux vetoScore _
            (restrictProfile (restrictProfile profile (0 : Fin 3)) c))) := by
    simpa [haux_restrict'] using hmem_sub
  rcases Finset.mem_biUnion.mp hmem_union with ⟨c, hcL, hmem_c'⟩
  have hc : c = cand1_0 := by
    simpa using (Finset.mem_singleton.mp hcL)
  subst hc
  have hnot :
      cand1_0 ∉
        liftFinset (scoringEliminationAux vetoScore _
          (restrictProfile (restrictProfile profile (0 : Fin 3)) cand1_0)) := by
    exact not_mem_liftFinset_removed (c := cand1_0)
      (s := scoringEliminationAux vetoScore _
        (restrictProfile (restrictProfile profile (0 : Fin 3)) cand1_0))
  exact (hnot hmem_c').elim

lemma coombs_profile_eq_singleton :
    coombs profile = ({2} : Finset (Fin 3)) := by
  classical
  ext x
  fin_cases x
  · constructor
    · intro hx
      exact (coombs_profile_not_0 hx).elim
    · intro hx
      simp at hx
  · constructor
    · intro hx
      exact (coombs_profile_not_1 hx).elim
    · intro hx
      simp at hx
  · simpa using coombs_profile_has_2

lemma reverse_profile_has_2 : (2 : Fin 3) ∈ coombs (reverse_profile profile) := by
  classical
  have hcoombs :
      coombs (reverse_profile profile) =
        scoringEliminationAux vetoScore (Fin 3) (reverse_profile profile) :=
    coombs_eq_aux (P := reverse_profile profile)
  have hcard : ¬ Fintype.card (Fin 3) ≤ 1 := by decide
  have haux :=
    scoringEliminationAux_eq_biUnion_of_not_card_le_one
      (score := vetoScore) (P := reverse_profile profile) (hcard := hcard)
  have haux' :
      scoringEliminationAux vetoScore (Fin 3) (reverse_profile profile) =
        (Finset.univ : Finset (Fin 3)).biUnion
          (fun c => liftFinset (scoringEliminationAux vetoScore _
            (restrictProfile (reverse_profile profile) c))) := by
    simpa [lowestScoring_reverse_profile_eq_univ] using haux
  have hmem_sub :
      cand2_1 ∈
        scoringEliminationAux vetoScore _
          (restrictProfile (reverse_profile profile) (1 : Fin 3)) := by
    have hcard' : ¬ Fintype.card {x : Fin 3 // x ≠ (1 : Fin 3)} ≤ 1 := by decide
    have haux_restrict :=
      scoringEliminationAux_eq_biUnion_of_not_card_le_one
        (score := vetoScore)
        (P := restrictProfile (reverse_profile profile) (1 : Fin 3)) (hcard := hcard')
    have haux_restrict' :
        scoringEliminationAux vetoScore _
          (restrictProfile (reverse_profile profile) (1 : Fin 3)) =
          (Finset.univ : Finset {x : Fin 3 // x ≠ (1 : Fin 3)}).biUnion
            (fun c => liftFinset (scoringEliminationAux vetoScore _
              (restrictProfile (restrictProfile (reverse_profile profile) (1 : Fin 3)) c))) := by
      simpa [lowestScoring_reverse_restrict_eq_univ] using haux_restrict
    have hbase :
        scoringEliminationAux vetoScore _
          (restrictProfile (restrictProfile (reverse_profile profile) (1 : Fin 3)) cand0_1) =
            (Finset.univ :
              Finset {x : {x : Fin 3 // x ≠ (1 : Fin 3)} // x ≠ cand0_1}) := by
      simp [scoringEliminationAux]
    have hmem_sub' :
        (⟨cand2_1, by decide⟩ :
            {x : {x : Fin 3 // x ≠ (1 : Fin 3)} // x ≠ cand0_1}) ∈
          scoringEliminationAux vetoScore _
            (restrictProfile (restrictProfile (reverse_profile profile) (1 : Fin 3)) cand0_1) := by
      simp [hbase]
    have hmem_lift :
        cand2_1 ∈
          liftFinset (scoringEliminationAux vetoScore _
            (restrictProfile (restrictProfile (reverse_profile profile) (1 : Fin 3)) cand0_1)) := by
      refine (mem_liftFinset_iff_subtype
        (s := scoringEliminationAux vetoScore _
          (restrictProfile (restrictProfile (reverse_profile profile) (1 : Fin 3)) cand0_1))
        (x := cand2_1)).2 ?_
      refine ⟨by decide, ?_⟩
      simpa using hmem_sub'
    have hmem_union :
        cand2_1 ∈
          (Finset.univ : Finset {x : Fin 3 // x ≠ (1 : Fin 3)}).biUnion
            (fun c => liftFinset (scoringEliminationAux vetoScore _
              (restrictProfile (restrictProfile (reverse_profile profile) (1 : Fin 3)) c))) := by
      refine Finset.mem_biUnion.mpr ?_
      exact ⟨cand0_1, by simp, hmem_lift⟩
    simpa [haux_restrict'] using hmem_union
  have hmem_lift0 :
      (2 : Fin 3) ∈
        liftFinset (scoringEliminationAux vetoScore _
          (restrictProfile (reverse_profile profile) (1 : Fin 3))) := by
    refine (mem_liftFinset_iff_subtype
      (s := scoringEliminationAux vetoScore _
        (restrictProfile (reverse_profile profile) (1 : Fin 3)))
      (x := (2 : Fin 3))).2 ?_
    refine ⟨by decide, ?_⟩
    have hx' :
        (⟨2, by decide⟩ : {x : Fin 3 // x ≠ (1 : Fin 3)}) = cand2_1 := by
      rfl
    simpa [hx'] using hmem_sub
  have hmem_union0 :
      (2 : Fin 3) ∈
        (Finset.univ : Finset (Fin 3)).biUnion
          (fun c => liftFinset (scoringEliminationAux vetoScore _
            (restrictProfile (reverse_profile profile) c))) := by
    refine Finset.mem_biUnion.mpr ?_
    exact ⟨(1 : Fin 3), by simp, hmem_lift0⟩
  simpa [hcoombs, haux'] using hmem_union0

end CoombsReversalCounterexample

theorem coombs_not_singletonReversalSymmetry : ¬ SingletonReversalSymmetry coombs := by
  intro h
  have hsingle :
      coombs CoombsReversalCounterexample.profile = {2} :=
    CoombsReversalCounterexample.coombs_profile_eq_singleton
  have hne : ∃ y : Fin 3, (2 : Fin 3) ≠ y := by
    exact ⟨0, by decide⟩
  have hnot :=
    h (P := CoombsReversalCounterexample.profile) (x := (2 : Fin 3)) hne hsingle
  have hw :
      (2 : Fin 3) ∈ coombs (reverse_profile CoombsReversalCounterexample.profile) :=
    CoombsReversalCounterexample.reverse_profile_has_2
  exact hnot hw

end SocialChoice
