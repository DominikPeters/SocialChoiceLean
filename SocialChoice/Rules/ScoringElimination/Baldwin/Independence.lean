import Mathlib.Tactic
import Mathlib.Tactic.FinCases
import SocialChoice.Axioms.Clones
import SocialChoice.Axioms.Independence
import SocialChoice.ListBallot
import SocialChoice.ListBallotProfiles
import SocialChoice.Profile
import SocialChoice.Rules.ScoringElimination.Basic
import SocialChoice.Rules.ScoringElimination.Baldwin.Defs

namespace SocialChoice

open Classical
open Finset

attribute [instance] Classical.decEq Classical.decPred

/-!
## Baldwin fails independence of dominated alternatives and independence of clones

Counterexample with 4 candidates (0,1,2,3) and 4 voters:
1 voter: 1 > 3 > 2 > 0
2 voters: 2 > 0 > 1 > 3
1 voter: 3 > 2 > 0 > 1

Candidate 0 is Pareto-dominated by 2. Baldwin selects {2,3}, but after
removing 0, Baldwin selects {2}. The clone set is {0,2}; removing clone 0
eliminates non-clone winner 3.
-/

namespace BaldwinIndependenceCounterexample

-- Ballots

def ballot1320 : ListBallot 4 := ListBallot.mk' [1, 3, 2, 0]
def ballot2013 : ListBallot 4 := ListBallot.mk' [2, 0, 1, 3]
def ballot3201 : ListBallot 4 := ListBallot.mk' [3, 2, 0, 1]

def ballots : Fin 4 → ListBallot 4
  | ⟨0, _⟩ => ballot1320
  | ⟨1, _⟩ => ballot2013
  | ⟨2, _⟩ => ballot2013
  | ⟨3, _⟩ => ballot3201

noncomputable def profile : Profile (Fin 4) (Fin 4) :=
  profileOfListBallots ballots

noncomputable def profile0 : Profile (Fin 4) {x : Fin 4 // x ≠ (0 : Fin 4)} :=
  restrictProfile profile (0 : Fin 4)

noncomputable def profile1 : Profile (Fin 4) {x : Fin 4 // x ≠ (1 : Fin 4)} :=
  restrictProfile profile (1 : Fin 4)

def cand3_0 : {x : Fin 4 // x ≠ (0 : Fin 4)} := ⟨3, by decide⟩

def cand0_1 : {x : Fin 4 // x ≠ (1 : Fin 4)} := ⟨0, by decide⟩
def cand2_1 : {x : Fin 4 // x ≠ (1 : Fin 4)} := ⟨2, by decide⟩
def cand3_1 : {x : Fin 4 // x ≠ (1 : Fin 4)} := ⟨3, by decide⟩

noncomputable def profile1_0 :
    Profile (Fin 4) {x : {x : Fin 4 // x ≠ (1 : Fin 4)} // x ≠ cand0_1} :=
  restrictProfile profile1 cand0_1

def cand2_1_0 : {x : {x : Fin 4 // x ≠ (1 : Fin 4)} // x ≠ cand0_1} :=
  ⟨cand2_1, by decide⟩

def cand3_1_0 : {x : {x : Fin 4 // x ≠ (1 : Fin 4)} // x ≠ cand0_1} :=
  ⟨cand3_1, by decide⟩

def cand3_1_0_2 :
    {x : {x : {x : Fin 4 // x ≠ (1 : Fin 4)} // x ≠ cand0_1} // x ≠ cand2_1_0} :=
  ⟨cand3_1_0, by decide⟩

@[reducible] noncomputable def scoreVec : Nat → Int := fun r =>
  bordaScore (Fintype.card (Fin 4)) r

@[reducible] noncomputable def scoreVec0 : Nat → Int := fun r =>
  bordaScore (Fintype.card {x : Fin 4 // x ≠ (0 : Fin 4)}) r

@[reducible] noncomputable def scoreVec1 : Nat → Int := fun r =>
  bordaScore (Fintype.card {x : Fin 4 // x ≠ (1 : Fin 4)}) r

@[reducible] noncomputable def scoreVec1_0 : Nat → Int := fun r =>
  bordaScore (Fintype.card {x : {x : Fin 4 // x ≠ (1 : Fin 4)} // x ≠ cand0_1}) r

private lemma baldwin_eq_aux {V A : Type} [Fintype V] [Fintype A] [DecidableEq A]
    (P : Profile V A) :
    baldwin P = scoringEliminationAux bordaScore A P := by
  classical
  simpa [baldwin, scoringEliminationRule] using
    (scoringEliminationAux_decidableEq_congr (score := bordaScore) (P := P)
      (inst1 := Classical.decEq A) (inst2 := inferInstance))

lemma prefers_2_0 : ∀ v : Fin 4, Prefers profile v (2 : Fin 4) (0 : Fin 4) := by
  intro v
  fin_cases v <;>
    simp [profile, ballots, prefers_iff_prefersInList, prefersInList] <;> decide

lemma lowestScoring_profile_eq :
    lowestScoring profile scoreVec = ({0, 1, 3} : Finset (Fin 4)) := by
  decide

lemma lowestScoring_profile0_eq :
    lowestScoring profile0 scoreVec0 = ({cand3_0} : Finset {x : Fin 4 // x ≠ (0 : Fin 4)}) := by
  decide

lemma lowestScoring_profile1_eq :
    lowestScoring profile1 scoreVec1 = ({cand0_1} : Finset {x : Fin 4 // x ≠ (1 : Fin 4)}) := by
  decide

lemma lowestScoring_profile1_0_eq :
    lowestScoring profile1_0 scoreVec1_0 =
      ({cand2_1_0, cand3_1_0} : Finset {x : {x : Fin 4 // x ≠ (1 : Fin 4)} // x ≠ cand0_1}) := by
  decide

lemma baldwin_profile1_0_has_3 :
    cand3_1_0 ∈ scoringEliminationAux bordaScore _ profile1_0 := by
  classical
  have hcard : ¬ Fintype.card {x : {x : Fin 4 // x ≠ (1 : Fin 4)} // x ≠ cand0_1} ≤ 1 := by
    decide
  have haux :=
    scoringEliminationAux_eq_biUnion_of_not_card_le_one
      (score := bordaScore) (P := profile1_0) (hcard := hcard)
  have haux' :
      scoringEliminationAux bordaScore _ profile1_0 =
        (lowestScoring profile1_0 scoreVec1_0).biUnion
          (fun c => liftFinset (scoringEliminationAux bordaScore _ (restrictProfile profile1_0 c))) := by
    exact haux
  have hmem_lift :
      cand3_1_0 ∈
        liftFinset (scoringEliminationAux bordaScore _ (restrictProfile profile1_0 cand2_1_0)) := by
    have hcard1 :
        Fintype.card {x : {x : {x : Fin 4 // x ≠ (1 : Fin 4)} // x ≠ cand0_1} // x ≠ cand2_1_0} ≤ 1 := by
      decide
    have haux1 :
        scoringEliminationAux bordaScore _ (restrictProfile profile1_0 cand2_1_0) =
          (Finset.univ :
            Finset {x : {x : {x : Fin 4 // x ≠ (1 : Fin 4)} // x ≠ cand0_1} // x ≠ cand2_1_0}) := by
      simp [scoringEliminationAux]
    have hmem_univ :
        cand3_1_0_2 ∈ scoringEliminationAux bordaScore _ (restrictProfile profile1_0 cand2_1_0) := by
      simp [haux1]
    have hx : cand3_1_0 ≠ cand2_1_0 := by decide
    exact (mem_liftFinset_iff_subtype
      (s := scoringEliminationAux bordaScore _ (restrictProfile profile1_0 cand2_1_0))
      (x := cand3_1_0)).2 ⟨by simpa using hx, hmem_univ⟩
  have hmem_union :
      cand3_1_0 ∈
        ({cand2_1_0, cand3_1_0} : Finset _).biUnion
          (fun c => liftFinset (scoringEliminationAux bordaScore _ (restrictProfile profile1_0 c))) := by
    refine Finset.mem_biUnion.mpr ?_
    refine ⟨cand2_1_0, ?_, hmem_lift⟩
    simp
  have hmem_aux :
      cand3_1_0 ∈ scoringEliminationAux bordaScore _ profile1_0 := by
    simpa [haux', lowestScoring_profile1_0_eq] using hmem_union
  exact hmem_aux

lemma baldwin_profile1_has_3 : cand3_1 ∈ baldwin profile1 := by
  classical
  have hcard : ¬ Fintype.card {x : Fin 4 // x ≠ (1 : Fin 4)} ≤ 1 := by
    decide
  have haux :=
    scoringEliminationAux_eq_biUnion_of_not_card_le_one
      (score := bordaScore) (P := profile1) (hcard := hcard)
  have haux' :
      scoringEliminationAux bordaScore _ profile1 =
        (lowestScoring profile1 scoreVec1).biUnion
          (fun c => liftFinset (scoringEliminationAux bordaScore _ (restrictProfile profile1 c))) := by
    exact haux
  have hmem_lift :
      cand3_1 ∈
        liftFinset (scoringEliminationAux bordaScore _ (restrictProfile profile1 cand0_1)) := by
    have hmem_sub : cand3_1_0 ∈ scoringEliminationAux bordaScore _ profile1_0 :=
      baldwin_profile1_0_has_3
    have hcand :
        (⟨cand3_1, by decide⟩ : {x : {x : Fin 4 // x ≠ (1 : Fin 4)} // x ≠ cand0_1}) =
          cand3_1_0 := by
      apply Subtype.ext
      rfl
    exact (mem_liftFinset_iff_subtype
      (s := scoringEliminationAux bordaScore _ (restrictProfile profile1 cand0_1))
      (x := cand3_1)).2 ⟨by decide, by simpa only [profile1_0, hcand] using hmem_sub⟩
  have hmem_union :
      cand3_1 ∈
        ({cand0_1} : Finset _).biUnion
          (fun c => liftFinset (scoringEliminationAux bordaScore _ (restrictProfile profile1 c))) := by
    refine Finset.mem_biUnion.mpr ?_
    refine ⟨cand0_1, by simp, hmem_lift⟩
  have hmem_aux :
      cand3_1 ∈ scoringEliminationAux bordaScore _ profile1 := by
    simpa [haux', lowestScoring_profile1_eq] using hmem_union
  simpa [baldwin_eq_aux] using hmem_aux

lemma baldwin_profile_has_3 : (3 : Fin 4) ∈ baldwin profile := by
  classical
  have hcard : ¬ Fintype.card (Fin 4) ≤ 1 := by
    decide
  have haux :=
    scoringEliminationAux_eq_biUnion_of_not_card_le_one
      (score := bordaScore) (P := profile) (hcard := hcard)
  have haux' :
      scoringEliminationAux bordaScore (Fin 4) profile =
        (lowestScoring profile scoreVec).biUnion
          (fun c => liftFinset (scoringEliminationAux bordaScore _ (restrictProfile profile c))) := by
    exact haux
  have hmem_lift :
      (3 : Fin 4) ∈
        liftFinset (scoringEliminationAux bordaScore _ (restrictProfile profile (1 : Fin 4))) := by
    have hmem_sub : cand3_1 ∈ baldwin profile1 := baldwin_profile1_has_3
    have hmem_sub' :
        cand3_1 ∈ scoringEliminationAux bordaScore _ (restrictProfile profile (1 : Fin 4)) := by
      simpa [baldwin_eq_aux, profile1] using hmem_sub
    exact (mem_liftFinset_iff_subtype
      (s := scoringEliminationAux bordaScore _ (restrictProfile profile (1 : Fin 4)))
      (x := (3 : Fin 4))).2 ⟨by decide, hmem_sub'⟩
  have hmem_union :
      (3 : Fin 4) ∈
        ({0, 1, 3} : Finset (Fin 4)).biUnion
          (fun c => liftFinset (scoringEliminationAux bordaScore _ (restrictProfile profile c))) := by
    refine Finset.mem_biUnion.mpr ?_
    refine ⟨(1 : Fin 4), ?_, hmem_lift⟩
    simp
  have hmem_aux :
      (3 : Fin 4) ∈ scoringEliminationAux bordaScore (Fin 4) profile := by
    simpa [haux', lowestScoring_profile_eq] using hmem_union
  simpa [baldwin_eq_aux] using hmem_aux

lemma baldwin_profile0_not_3 : cand3_0 ∉ baldwin profile0 := by
  classical
  have hcard : ¬ Fintype.card {x : Fin 4 // x ≠ (0 : Fin 4)} ≤ 1 := by
    decide
  have haux :=
    scoringEliminationAux_eq_biUnion_of_not_card_le_one
      (score := bordaScore) (P := profile0) (hcard := hcard)
  have haux' :
      scoringEliminationAux bordaScore _ profile0 =
        (lowestScoring profile0 scoreVec0).biUnion
          (fun c => liftFinset (scoringEliminationAux bordaScore _ (restrictProfile profile0 c))) := by
    exact haux
  have hbaldwin :
      baldwin profile0 = scoringEliminationAux bordaScore _ profile0 :=
    baldwin_eq_aux (P := profile0)
  intro hmem
  have hmem' :
      cand3_0 ∈
        (lowestScoring profile0 scoreVec0).biUnion
          (fun c => liftFinset (scoringEliminationAux bordaScore _ (restrictProfile profile0 c))) := by
    simpa [hbaldwin, haux'] using hmem
  have hmem'' :
      cand3_0 ∈
        ({cand3_0} : Finset _).biUnion
          (fun c => liftFinset (scoringEliminationAux bordaScore _ (restrictProfile profile0 c))) := by
    simpa [lowestScoring_profile0_eq] using hmem'
  rcases Finset.mem_biUnion.mp hmem'' with ⟨c, hcL, hmemc⟩
  have hc : c = cand3_0 := by
    simpa using (Finset.mem_singleton.mp hcL)
  subst hc
  have hnot :
      cand3_0 ∉
        liftFinset (scoringEliminationAux bordaScore _ (restrictProfile profile0 cand3_0)) := by
    exact not_mem_liftFinset_removed
      (s := scoringEliminationAux bordaScore _ (restrictProfile profile0 cand3_0))
  exact hnot hmemc

lemma mem_liftWinners_iff {A : Type} [DecidableEq A] {p : A → Prop} [DecidablePred p]
    {s : Finset {a : A // p a}} {x : A} (hx : p x) :
    x ∈ liftWinners s ↔ (⟨x, hx⟩ : {a : A // p a}) ∈ s := by
  classical
  simp [liftWinners, Finset.mem_image, hx]

-- Clone set {0,2}

def cloneSet : Set (Fin 4) := {0, 2}

lemma cloneSet_profile : CloneSet profile cloneSet := by
  refine ⟨?_, ?_⟩
  · refine ⟨(0 : Fin 4), by simp [cloneSet]⟩
  intro v c hc
  fin_cases c
  · exact (hc (by simp [cloneSet])).elim
  · -- c = 1
    fin_cases v <;>
      (first
        | right
          intro x hx
          have hx' : x = (0 : Fin 4) ∨ x = (2 : Fin 4) := by
            simpa [cloneSet] using hx
          cases hx' with
          | inl hx0 =>
              subst hx0
              simp [profile, ballots, prefers_iff_prefersInList, prefersInList]; decide
          | inr hx2 =>
              subst hx2
              simp [profile, ballots, prefers_iff_prefersInList, prefersInList]; decide
        | left
          intro x hx
          have hx' : x = (0 : Fin 4) ∨ x = (2 : Fin 4) := by
            simpa [cloneSet] using hx
          cases hx' with
          | inl hx0 =>
              subst hx0
              simp [profile, ballots, prefers_iff_prefersInList, prefersInList]; decide
          | inr hx2 =>
              subst hx2
              simp [profile, ballots, prefers_iff_prefersInList, prefersInList]; decide)
  · exact (hc (by simp [cloneSet])).elim
  · -- c = 3
    fin_cases v <;>
      (first
        | right
          intro x hx
          have hx' : x = (0 : Fin 4) ∨ x = (2 : Fin 4) := by
            simpa [cloneSet] using hx
          cases hx' with
          | inl hx0 =>
              subst hx0
              simp [profile, ballots, prefers_iff_prefersInList, prefersInList]; decide
          | inr hx2 =>
              subst hx2
              simp [profile, ballots, prefers_iff_prefersInList, prefersInList]; decide
        | left
          intro x hx
          have hx' : x = (0 : Fin 4) ∨ x = (2 : Fin 4) := by
            simpa [cloneSet] using hx
          cases hx' with
          | inl hx0 =>
              subst hx0
              simp [profile, ballots, prefers_iff_prefersInList, prefersInList]; decide
          | inr hx2 =>
              subst hx2
              simp [profile, ballots, prefers_iff_prefersInList, prefersInList]; decide)

lemma b_not_mem_cloneSet : (3 : Fin 4) ∉ cloneSet := by
  simp [cloneSet]

lemma c_mem_cloneSet : (2 : Fin 4) ∈ cloneSet := by
  simp [cloneSet]

lemma clonePred_eq_ne :
    clonePred cloneSet (2 : Fin 4) = (fun x : Fin 4 => x ≠ (0 : Fin 4)) := by
  funext x
  apply propext
  fin_cases x <;> simp [cloneSet, clonePred]

def cand3clone : {a : Fin 4 // clonePred cloneSet (2 : Fin 4) a} :=
  ⟨3, Or.inl b_not_mem_cloneSet⟩

lemma cast_subtype_val {A : Type} {p q : A → Prop}
    (h : p = q) (x : {a : A // p a}) :
    (cast (congrArg (fun r => {a : A // r a}) h) x : {a : A // q a}).1 = x.1 := by
  cases x
  cases h
  rfl

lemma mem_castCandidates_iff {V A : Type} [Fintype V] [Fintype A]
    (f : VotingRule) {p q : A → Prop}
    (dp : DecidablePred p) (dq : DecidablePred q)
    (h : p = q) (x : {a : A // p a}) (P : Profile V {a : A // p a}) :
    x ∈ f P ↔
      ((cast (congrArg (fun r => {a : A // r a}) h) x : {a : A // q a}) ∈
        f (castCandidates (p := p) (q := q) h P)) := by
  classical
  letI : DecidablePred p := dp
  letI : DecidablePred q := dq
  cases h
  cases (Subsingleton.elim dq dp)
  rfl

lemma baldwin_cloneProfile_not_3_raw :
    cand3clone ∉ baldwin (removeClonesExcept profile cloneSet (2 : Fin 4)) := by
  classical
  let q : Fin 4 → Prop := fun x => x ≠ (0 : Fin 4)
  have hnot : cand3_0 ∉ baldwin (restrictCandidates profile q) := by
    simpa [profile0, restrictProfile, q] using baldwin_profile0_not_3
  have hpred : q = clonePred cloneSet (2 : Fin 4) := by
    simpa [q] using clonePred_eq_ne.symm
  have hmem_cast :
      (cast (congrArg (fun r => {a : Fin 4 // r a}) hpred) cand3_0 :
        {a : Fin 4 // clonePred cloneSet (2 : Fin 4) a}) ∉
        baldwin (castCandidates (p := q) (q := clonePred cloneSet (2 : Fin 4)) hpred
          (restrictCandidates profile q)) := by
    intro hmem
    have hmem' : cand3_0 ∈ baldwin (restrictCandidates profile q) :=
      (mem_castCandidates_iff (f := baldwin)
        (dp := inferInstance) (dq := inferInstance) (h := hpred)
        (x := cand3_0) (P := restrictCandidates profile q)).2 hmem
    exact hnot hmem'
  have hmem_cast' :
      (cast (congrArg (fun r => {a : Fin 4 // r a}) hpred) cand3_0 :
        {a : Fin 4 // clonePred cloneSet (2 : Fin 4) a}) ∉
        baldwin (restrictCandidates profile (clonePred cloneSet (2 : Fin 4))) := by
    simpa [castCandidates_restrictCandidates] using hmem_cast
  have hcast_cand3 :
      (cast (congrArg (fun r => {a : Fin 4 // r a}) hpred) cand3_0 :
        {a : Fin 4 // clonePred cloneSet (2 : Fin 4) a}) = cand3clone := by
    apply Subtype.ext
    simpa [cand3clone, cand3_0] using (cast_subtype_val (h := hpred) (x := cand3_0))
  have hfinal :
      cand3clone ∉ baldwin (restrictCandidates profile (clonePred cloneSet (2 : Fin 4))) := by
    simpa [hcast_cand3] using hmem_cast'
  simpa [removeClonesExcept] using hfinal

lemma baldwin_cloneProfile_not_3 :
    (⟨3, Or.inl b_not_mem_cloneSet⟩ :
        {a : Fin 4 // clonePred cloneSet (2 : Fin 4) a}) ∉
      baldwin (removeClonesExcept profile cloneSet (2 : Fin 4)) := by
  simpa [cand3clone] using baldwin_cloneProfile_not_3_raw

end BaldwinIndependenceCounterexample

open BaldwinIndependenceCounterexample

theorem baldwin_not_independenceOfDominated : ¬ IndependenceOfDominated baldwin := by
  intro hind
  have hpref : ∀ v : Fin 4, Prefers profile v (2 : Fin 4) (0 : Fin 4) :=
    prefers_2_0
  have hEq := hind (P := profile) (c := (2 : Fin 4)) (d := (0 : Fin 4)) hpref
  have hmem : (3 : Fin 4) ∈ baldwin profile := baldwin_profile_has_3
  have hmem' :
      (3 : Fin 4) ∈ liftWinners (baldwin (restrictCandidates profile (fun a => a ≠ (0 : Fin 4)))) := by
    simpa [hEq] using hmem
  have hnot :
      (3 : Fin 4) ∉ liftWinners (baldwin (restrictCandidates profile (fun a => a ≠ (0 : Fin 4)))) := by
    have hnot' : cand3_0 ∉ baldwin profile0 := baldwin_profile0_not_3
    have hnot'' :
        (3 : Fin 4) ∉ liftWinners (baldwin profile0) := by
      intro h
      have h' : cand3_0 ∈ baldwin profile0 :=
        (mem_liftWinners_iff (p := fun a : Fin 4 => a ≠ (0 : Fin 4))
          (s := baldwin profile0) (x := (3 : Fin 4)) (by decide)).1 h
      exact hnot' h'
    simpa [profile0, restrictProfile] using hnot''
  exact (hnot hmem').elim

theorem baldwin_not_independenceOfClones : ¬ IndependenceOfClones baldwin := by
  intro hind
  have hclone : CloneSet profile cloneSet := cloneSet_profile
  have hx : (2 : Fin 4) ∈ cloneSet := c_mem_cloneSet
  have h := hind (P := profile) (X := cloneSet) (x := (2 : Fin 4)) hclone hx
  have hc : (3 : Fin 4) ∉ cloneSet := b_not_mem_cloneSet
  have hnonclone := h.1 (3 : Fin 4) hc
  have hleft : (3 : Fin 4) ∈ baldwin profile := baldwin_profile_has_3
  have hright :
      (⟨3, Or.inl hc⟩ : {a : Fin 4 // clonePred cloneSet (2 : Fin 4) a}) ∉
        baldwin (removeClonesExcept profile cloneSet (2 : Fin 4)) := by
    have hsub :
        (⟨3, Or.inl hc⟩ : {a : Fin 4 // clonePred cloneSet (2 : Fin 4) a}) =
          (⟨3, Or.inl b_not_mem_cloneSet⟩ :
            {a : Fin 4 // clonePred cloneSet (2 : Fin 4) a}) := by
      apply Subtype.ext
      rfl
    simpa [hsub] using baldwin_cloneProfile_not_3
  have hcontr : (3 : Fin 4) ∉ baldwin profile := by
    intro hmem
    have hmem' :
        (⟨3, Or.inl hc⟩ : {a : Fin 4 // clonePred cloneSet (2 : Fin 4) a}) ∈
          baldwin (removeClonesExcept profile cloneSet (2 : Fin 4)) :=
      (hnonclone).1 hmem
    exact hright hmem'
  exact (hcontr hleft).elim

end SocialChoice
