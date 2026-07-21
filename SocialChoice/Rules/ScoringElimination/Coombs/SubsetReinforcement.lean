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

open Classical
attribute [instance] Classical.decEq Classical.decPred

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

def ballots2_1 : Fin 2 → ListBallot 3
  | 0 => ballot102
  | 1 => ballot201

def ballots2_2 : Fin 2 → ListBallot 3
  | 0 => ballot120
  | 1 => ballot201

section BallotHelpers

variable {V : Type} [Fintype V]

noncomputable def profileOfBallots (ballots : V → ListBallot 3) : Profile V (Fin 3) :=
  { pref := fun v => (ballots v).toLinearOrder }

end BallotHelpers

def voters1 : Finset (Fin 4) := {0, 1}
def voters2 : Finset (Fin 4) := {2, 3}

def ballots1 (v : Electorate (Fin 4) voters1) : ListBallot 3 := ballots4 v.1
def ballots2 (v : Electorate (Fin 4) voters2) : ListBallot 3 := ballots4 v.1
def ballotsAll (v : Electorate (Fin 4) (voters1 ∪ voters2)) : ListBallot 3 := ballots4 v.1

noncomputable def profile1 : Profile (Electorate (Fin 4) voters1) (Fin 3) :=
  profileOfBallots ballots1

noncomputable def profile2 : Profile (Electorate (Fin 4) voters2) (Fin 3) :=
  profileOfBallots ballots2

noncomputable def profileAll :
    Profile (Electorate (Fin 4) (voters1 ∪ voters2)) (Fin 3) :=
  profileOfBallots ballotsAll

noncomputable def profile1_list : Profile (Fin 2) (Fin 3) :=
  profileOfListBallots ballots2_1

noncomputable def profile2_list : Profile (Fin 2) (Fin 3) :=
  profileOfListBallots ballots2_2

noncomputable def profileAll_list : Profile (Fin 4) (Fin 3) :=
  profileOfListBallots ballots4

lemma voters1_disjoint_voters2 : Disjoint voters1 voters2 := by
  classical
  decide

lemma votersAll_eq : voters1 ∪ voters2 = (Finset.univ : Finset (Fin 4)) := by
  ext v
  fin_cases v <;> simp [voters1, voters2]

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

noncomputable def e1_to : Fin 2 → Electorate (Fin 4) voters1
  | ⟨0, _⟩ => ⟨0, by simp [voters1]⟩
  | ⟨1, _⟩ => ⟨1, by simp [voters1]⟩

noncomputable def e1_inv : Electorate (Fin 4) voters1 → Fin 2
  | ⟨0, _⟩ => ⟨0, by decide⟩
  | ⟨1, _⟩ => ⟨1, by decide⟩
  | ⟨2, h⟩ => (False.elim (by simp [voters1] at h))
  | ⟨3, h⟩ => (False.elim (by simp [voters1] at h))

noncomputable def e1 : Fin 2 ≃ Electorate (Fin 4) voters1 :=
  { toFun := e1_to
    invFun := e1_inv
    left_inv := by
      intro v
      fin_cases v <;> rfl
    right_inv := by
      intro v
      cases v with
      | mk val hmem =>
          fin_cases val <;> simp [e1_to, e1_inv, voters1] at hmem ⊢ }

noncomputable def e2_to : Fin 2 → Electorate (Fin 4) voters2
  | ⟨0, _⟩ => ⟨2, by simp [voters2]⟩
  | ⟨1, _⟩ => ⟨3, by simp [voters2]⟩

noncomputable def e2_inv : Electorate (Fin 4) voters2 → Fin 2
  | ⟨2, _⟩ => ⟨0, by decide⟩
  | ⟨3, _⟩ => ⟨1, by decide⟩
  | ⟨0, h⟩ => (False.elim (by simp [voters2] at h))
  | ⟨1, h⟩ => (False.elim (by simp [voters2] at h))

noncomputable def e2 : Fin 2 ≃ Electorate (Fin 4) voters2 :=
  { toFun := e2_to
    invFun := e2_inv
    left_inv := by
      intro v
      fin_cases v <;> rfl
    right_inv := by
      intro v
      cases v with
      | mk val hmem =>
          fin_cases val <;> simp [e2_to, e2_inv, voters2] at hmem ⊢ }

noncomputable def e4 : Fin 4 ≃ Electorate (Fin 4) (voters1 ∪ voters2) :=
  { toFun := fun x => ⟨x, by simp [votersAll_eq]⟩
    invFun := fun v => v.1
    left_inv := by intro x; rfl
    right_inv := by intro v; cases v; rfl }

lemma relabel_profile1_eq_profile1_list :
    relabelProfileVoters e1 profile1 = profile1_list := by
  ext v
  fin_cases v <;> rfl

lemma relabel_profile2_eq_profile2_list :
    relabelProfileVoters e2 profile2 = profile2_list := by
  ext v
  fin_cases v <;> rfl

lemma relabel_profileAll_eq_profileAll_list :
    relabelProfileVoters e4 profileAll = profileAll_list := by
  ext v
  rfl

lemma scoreCandidate_relabelProfileVoters {V W A : Type} [Fintype V] [Fintype W] [Fintype A]
    (e : W ≃ V) (P : Profile V A) (score : Nat → Int) (c : A) :
    scoreCandidate (relabelProfileVoters e P) score c = scoreCandidate P score c := by
  classical
  unfold scoreCandidate relabelProfileVoters
  refine Finset.sum_bij (fun w _ => e w) ?_ ?_ ?_ ?_
  · intro w hw
    simp
  · intro w1 _ w2 _ h
    exact e.injective h
  · intro v hv
    refine ⟨e.symm v, by simp, by simp⟩
  · intro w hw
    simp

lemma notBottom_card {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (c : A) {k : Nat} (hcard : (votersBottom P c).card = k) :
    (Finset.univ.filter (fun v => ¬ BottomRank P v c)).card = Fintype.card V - k := by
  classical
  have hsum :
      (Finset.univ.filter (fun v => BottomRank P v c)).card +
        (Finset.univ.filter (fun v => ¬ BottomRank P v c)).card =
        (Finset.univ : Finset V).card := by
    simpa using
      (Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset V)) (p := fun v => BottomRank P v c))
  have hbottom :
      (Finset.univ.filter (fun v => BottomRank P v c)).card = k := by
    simpa [votersBottom] using hcard
  have hcardV : (Finset.univ : Finset V).card = Fintype.card V := by
    simp
  have hsum' :
      k + (Finset.univ.filter (fun v => ¬ BottomRank P v c)).card = Fintype.card V := by
    simpa [hbottom, hcardV] using hsum
  calc
    (Finset.univ.filter (fun v => ¬ BottomRank P v c)).card =
        k + (Finset.univ.filter (fun v => ¬ BottomRank P v c)).card - k := by
          symm
          simp
    _ = Fintype.card V - k := by
          simp [hsum']

@[reducible] def scoreVec : Nat → Int := fun r => vetoScore (Fintype.card (Fin 3)) r

lemma votersBottom_profile1_list_0_card :
    (votersBottom profile1_list (0 : Fin 3)).card = 0 := by
  have h : countBottom (fun v => (ballots2_1 v).ranking) (0 : Fin 3) = 0 := by decide
  calc
    (votersBottom profile1_list (0 : Fin 3)).card =
        countBottom (fun v => (ballots2_1 v).ranking) (0 : Fin 3) := by
          simpa [profile1_list] using
            (votersBottom_card_eq_countBottom (ballots := ballots2_1) (c := (0 : Fin 3)))
    _ = 0 := h

lemma votersBottom_profile1_list_1_card :
    (votersBottom profile1_list (1 : Fin 3)).card = 1 := by
  have h : countBottom (fun v => (ballots2_1 v).ranking) (1 : Fin 3) = 1 := by decide
  calc
    (votersBottom profile1_list (1 : Fin 3)).card =
        countBottom (fun v => (ballots2_1 v).ranking) (1 : Fin 3) := by
          simpa [profile1_list] using
            (votersBottom_card_eq_countBottom (ballots := ballots2_1) (c := (1 : Fin 3)))
    _ = 1 := h

lemma votersBottom_profile1_list_2_card :
    (votersBottom profile1_list (2 : Fin 3)).card = 1 := by
  have h : countBottom (fun v => (ballots2_1 v).ranking) (2 : Fin 3) = 1 := by decide
  calc
    (votersBottom profile1_list (2 : Fin 3)).card =
        countBottom (fun v => (ballots2_1 v).ranking) (2 : Fin 3) := by
          simpa [profile1_list] using
            (votersBottom_card_eq_countBottom (ballots := ballots2_1) (c := (2 : Fin 3)))
    _ = 1 := h

lemma votersBottom_profile2_list_0_card :
    (votersBottom profile2_list (0 : Fin 3)).card = 1 := by
  have h : countBottom (fun v => (ballots2_2 v).ranking) (0 : Fin 3) = 1 := by decide
  calc
    (votersBottom profile2_list (0 : Fin 3)).card =
        countBottom (fun v => (ballots2_2 v).ranking) (0 : Fin 3) := by
          simpa [profile2_list] using
            (votersBottom_card_eq_countBottom (ballots := ballots2_2) (c := (0 : Fin 3)))
    _ = 1 := h

lemma votersBottom_profile2_list_1_card :
    (votersBottom profile2_list (1 : Fin 3)).card = 1 := by
  have h : countBottom (fun v => (ballots2_2 v).ranking) (1 : Fin 3) = 1 := by decide
  calc
    (votersBottom profile2_list (1 : Fin 3)).card =
        countBottom (fun v => (ballots2_2 v).ranking) (1 : Fin 3) := by
          simpa [profile2_list] using
            (votersBottom_card_eq_countBottom (ballots := ballots2_2) (c := (1 : Fin 3)))
    _ = 1 := h

lemma votersBottom_profile2_list_2_card :
    (votersBottom profile2_list (2 : Fin 3)).card = 0 := by
  have h : countBottom (fun v => (ballots2_2 v).ranking) (2 : Fin 3) = 0 := by decide
  calc
    (votersBottom profile2_list (2 : Fin 3)).card =
        countBottom (fun v => (ballots2_2 v).ranking) (2 : Fin 3) := by
          simpa [profile2_list] using
            (votersBottom_card_eq_countBottom (ballots := ballots2_2) (c := (2 : Fin 3)))
    _ = 0 := h

lemma votersBottom_profileAll_list_0_card :
    (votersBottom profileAll_list (0 : Fin 3)).card = 1 := by
  have h : countBottom (fun v => (ballots4 v).ranking) (0 : Fin 3) = 1 := by decide
  calc
    (votersBottom profileAll_list (0 : Fin 3)).card =
        countBottom (fun v => (ballots4 v).ranking) (0 : Fin 3) := by
          simpa [profileAll_list] using
            (votersBottom_card_eq_countBottom (ballots := ballots4) (c := (0 : Fin 3)))
    _ = 1 := h

lemma votersBottom_profileAll_list_1_card :
    (votersBottom profileAll_list (1 : Fin 3)).card = 2 := by
  have h : countBottom (fun v => (ballots4 v).ranking) (1 : Fin 3) = 2 := by decide
  calc
    (votersBottom profileAll_list (1 : Fin 3)).card =
        countBottom (fun v => (ballots4 v).ranking) (1 : Fin 3) := by
          simpa [profileAll_list] using
            (votersBottom_card_eq_countBottom (ballots := ballots4) (c := (1 : Fin 3)))
    _ = 2 := h

lemma votersBottom_profileAll_list_2_card :
    (votersBottom profileAll_list (2 : Fin 3)).card = 1 := by
  have h : countBottom (fun v => (ballots4 v).ranking) (2 : Fin 3) = 1 := by decide
  calc
    (votersBottom profileAll_list (2 : Fin 3)).card =
        countBottom (fun v => (ballots4 v).ranking) (2 : Fin 3) := by
          simpa [profileAll_list] using
            (votersBottom_card_eq_countBottom (ballots := ballots4) (c := (2 : Fin 3)))
    _ = 1 := h

lemma scoreCandidate_profile1_list_0 :
    scoreCandidate profile1_list scoreVec (0 : Fin 3) = (2 : Int) := by
  have hbottom : (votersBottom profile1_list (0 : Fin 3)).card = 0 :=
    votersBottom_profile1_list_0_card
  have hnotBottom :
      (Finset.univ.filter (fun v => ¬ BottomRank profile1_list v (0 : Fin 3))).card = 2 := by
    simpa using (notBottom_card (P := profile1_list) (c := (0 : Fin 3)) (k := 0) hbottom)
  calc
    scoreCandidate profile1_list scoreVec (0 : Fin 3) =
        ((Finset.univ.filter (fun v => ¬ BottomRank profile1_list v (0 : Fin 3))).card : Int) := by
          exact
            (vetoScore_scoreCandidate_eq_notBottom_card (P := profile1_list) (c := (0 : Fin 3)))
    _ = (2 : Int) := by exact_mod_cast hnotBottom

lemma scoreCandidate_profile1_list_1 :
    scoreCandidate profile1_list scoreVec (1 : Fin 3) = (1 : Int) := by
  have hbottom : (votersBottom profile1_list (1 : Fin 3)).card = 1 :=
    votersBottom_profile1_list_1_card
  have hnotBottom :
      (Finset.univ.filter (fun v => ¬ BottomRank profile1_list v (1 : Fin 3))).card = 1 := by
    simpa using (notBottom_card (P := profile1_list) (c := (1 : Fin 3)) (k := 1) hbottom)
  calc
    scoreCandidate profile1_list scoreVec (1 : Fin 3) =
        ((Finset.univ.filter (fun v => ¬ BottomRank profile1_list v (1 : Fin 3))).card : Int) := by
          exact
            (vetoScore_scoreCandidate_eq_notBottom_card (P := profile1_list) (c := (1 : Fin 3)))
    _ = (1 : Int) := by exact_mod_cast hnotBottom

lemma scoreCandidate_profile1_list_2 :
    scoreCandidate profile1_list scoreVec (2 : Fin 3) = (1 : Int) := by
  have hbottom : (votersBottom profile1_list (2 : Fin 3)).card = 1 :=
    votersBottom_profile1_list_2_card
  have hnotBottom :
      (Finset.univ.filter (fun v => ¬ BottomRank profile1_list v (2 : Fin 3))).card = 1 := by
    simpa using (notBottom_card (P := profile1_list) (c := (2 : Fin 3)) (k := 1) hbottom)
  calc
    scoreCandidate profile1_list scoreVec (2 : Fin 3) =
        ((Finset.univ.filter (fun v => ¬ BottomRank profile1_list v (2 : Fin 3))).card : Int) := by
          exact
            (vetoScore_scoreCandidate_eq_notBottom_card (P := profile1_list) (c := (2 : Fin 3)))
    _ = (1 : Int) := by exact_mod_cast hnotBottom

lemma scoreCandidate_profile2_list_0 :
    scoreCandidate profile2_list scoreVec (0 : Fin 3) = (1 : Int) := by
  have hbottom : (votersBottom profile2_list (0 : Fin 3)).card = 1 :=
    votersBottom_profile2_list_0_card
  have hnotBottom :
      (Finset.univ.filter (fun v => ¬ BottomRank profile2_list v (0 : Fin 3))).card = 1 := by
    simpa using (notBottom_card (P := profile2_list) (c := (0 : Fin 3)) (k := 1) hbottom)
  calc
    scoreCandidate profile2_list scoreVec (0 : Fin 3) =
        ((Finset.univ.filter (fun v => ¬ BottomRank profile2_list v (0 : Fin 3))).card : Int) := by
          exact
            (vetoScore_scoreCandidate_eq_notBottom_card (P := profile2_list) (c := (0 : Fin 3)))
    _ = (1 : Int) := by exact_mod_cast hnotBottom

lemma scoreCandidate_profile2_list_1 :
    scoreCandidate profile2_list scoreVec (1 : Fin 3) = (1 : Int) := by
  have hbottom : (votersBottom profile2_list (1 : Fin 3)).card = 1 :=
    votersBottom_profile2_list_1_card
  have hnotBottom :
      (Finset.univ.filter (fun v => ¬ BottomRank profile2_list v (1 : Fin 3))).card = 1 := by
    simpa using (notBottom_card (P := profile2_list) (c := (1 : Fin 3)) (k := 1) hbottom)
  calc
    scoreCandidate profile2_list scoreVec (1 : Fin 3) =
        ((Finset.univ.filter (fun v => ¬ BottomRank profile2_list v (1 : Fin 3))).card : Int) := by
          exact
            (vetoScore_scoreCandidate_eq_notBottom_card (P := profile2_list) (c := (1 : Fin 3)))
    _ = (1 : Int) := by exact_mod_cast hnotBottom

lemma scoreCandidate_profile2_list_2 :
    scoreCandidate profile2_list scoreVec (2 : Fin 3) = (2 : Int) := by
  have hbottom : (votersBottom profile2_list (2 : Fin 3)).card = 0 :=
    votersBottom_profile2_list_2_card
  have hnotBottom :
      (Finset.univ.filter (fun v => ¬ BottomRank profile2_list v (2 : Fin 3))).card = 2 := by
    simpa using (notBottom_card (P := profile2_list) (c := (2 : Fin 3)) (k := 0) hbottom)
  calc
    scoreCandidate profile2_list scoreVec (2 : Fin 3) =
        ((Finset.univ.filter (fun v => ¬ BottomRank profile2_list v (2 : Fin 3))).card : Int) := by
          exact
            (vetoScore_scoreCandidate_eq_notBottom_card (P := profile2_list) (c := (2 : Fin 3)))
    _ = (2 : Int) := by exact_mod_cast hnotBottom

lemma scoreCandidate_profileAll_list_0 :
    scoreCandidate profileAll_list scoreVec (0 : Fin 3) = (3 : Int) := by
  have hbottom : (votersBottom profileAll_list (0 : Fin 3)).card = 1 :=
    votersBottom_profileAll_list_0_card
  have hnotBottom :
      (Finset.univ.filter (fun v => ¬ BottomRank profileAll_list v (0 : Fin 3))).card = 3 := by
    simpa using (notBottom_card (P := profileAll_list) (c := (0 : Fin 3)) (k := 1) hbottom)
  calc
    scoreCandidate profileAll_list scoreVec (0 : Fin 3) =
        ((Finset.univ.filter (fun v => ¬ BottomRank profileAll_list v (0 : Fin 3))).card : Int) := by
          exact
            (vetoScore_scoreCandidate_eq_notBottom_card (P := profileAll_list) (c := (0 : Fin 3)))
    _ = (3 : Int) := by exact_mod_cast hnotBottom

lemma scoreCandidate_profileAll_list_1 :
    scoreCandidate profileAll_list scoreVec (1 : Fin 3) = (2 : Int) := by
  have hbottom : (votersBottom profileAll_list (1 : Fin 3)).card = 2 :=
    votersBottom_profileAll_list_1_card
  have hnotBottom :
      (Finset.univ.filter (fun v => ¬ BottomRank profileAll_list v (1 : Fin 3))).card = 2 := by
    simpa using (notBottom_card (P := profileAll_list) (c := (1 : Fin 3)) (k := 2) hbottom)
  calc
    scoreCandidate profileAll_list scoreVec (1 : Fin 3) =
        ((Finset.univ.filter (fun v => ¬ BottomRank profileAll_list v (1 : Fin 3))).card : Int) := by
          exact
            (vetoScore_scoreCandidate_eq_notBottom_card (P := profileAll_list) (c := (1 : Fin 3)))
    _ = (2 : Int) := by exact_mod_cast hnotBottom

lemma scoreCandidate_profileAll_list_2 :
    scoreCandidate profileAll_list scoreVec (2 : Fin 3) = (3 : Int) := by
  have hbottom : (votersBottom profileAll_list (2 : Fin 3)).card = 1 :=
    votersBottom_profileAll_list_2_card
  have hnotBottom :
      (Finset.univ.filter (fun v => ¬ BottomRank profileAll_list v (2 : Fin 3))).card = 3 := by
    simpa using (notBottom_card (P := profileAll_list) (c := (2 : Fin 3)) (k := 1) hbottom)
  calc
    scoreCandidate profileAll_list scoreVec (2 : Fin 3) =
        ((Finset.univ.filter (fun v => ¬ BottomRank profileAll_list v (2 : Fin 3))).card : Int) := by
          exact
            (vetoScore_scoreCandidate_eq_notBottom_card (P := profileAll_list) (c := (2 : Fin 3)))
    _ = (3 : Int) := by exact_mod_cast hnotBottom

lemma scoreCandidate_profile1_0 :
    scoreCandidate profile1 scoreVec (0 : Fin 3) = (2 : Int) := by
  calc
    scoreCandidate profile1 scoreVec (0 : Fin 3) =
        scoreCandidate (relabelProfileVoters e1 profile1) scoreVec (0 : Fin 3) := by
          simpa using
            (scoreCandidate_relabelProfileVoters (e := e1) (P := profile1)
              (score := scoreVec) (c := (0 : Fin 3))).symm
    _ = (2 : Int) := by
          simpa [relabel_profile1_eq_profile1_list] using scoreCandidate_profile1_list_0

lemma scoreCandidate_profile1_1 :
    scoreCandidate profile1 scoreVec (1 : Fin 3) = (1 : Int) := by
  calc
    scoreCandidate profile1 scoreVec (1 : Fin 3) =
        scoreCandidate (relabelProfileVoters e1 profile1) scoreVec (1 : Fin 3) := by
          simpa using
            (scoreCandidate_relabelProfileVoters (e := e1) (P := profile1)
              (score := scoreVec) (c := (1 : Fin 3))).symm
    _ = (1 : Int) := by
          simpa [relabel_profile1_eq_profile1_list] using scoreCandidate_profile1_list_1

lemma scoreCandidate_profile1_2 :
    scoreCandidate profile1 scoreVec (2 : Fin 3) = (1 : Int) := by
  calc
    scoreCandidate profile1 scoreVec (2 : Fin 3) =
        scoreCandidate (relabelProfileVoters e1 profile1) scoreVec (2 : Fin 3) := by
          simpa using
            (scoreCandidate_relabelProfileVoters (e := e1) (P := profile1)
              (score := scoreVec) (c := (2 : Fin 3))).symm
    _ = (1 : Int) := by
          simpa [relabel_profile1_eq_profile1_list] using scoreCandidate_profile1_list_2

lemma scoreCandidate_profile2_0 :
    scoreCandidate profile2 scoreVec (0 : Fin 3) = (1 : Int) := by
  calc
    scoreCandidate profile2 scoreVec (0 : Fin 3) =
        scoreCandidate (relabelProfileVoters e2 profile2) scoreVec (0 : Fin 3) := by
          simpa using
            (scoreCandidate_relabelProfileVoters (e := e2) (P := profile2)
              (score := scoreVec) (c := (0 : Fin 3))).symm
    _ = (1 : Int) := by
          simpa [relabel_profile2_eq_profile2_list] using scoreCandidate_profile2_list_0

lemma scoreCandidate_profile2_1 :
    scoreCandidate profile2 scoreVec (1 : Fin 3) = (1 : Int) := by
  calc
    scoreCandidate profile2 scoreVec (1 : Fin 3) =
        scoreCandidate (relabelProfileVoters e2 profile2) scoreVec (1 : Fin 3) := by
          simpa using
            (scoreCandidate_relabelProfileVoters (e := e2) (P := profile2)
              (score := scoreVec) (c := (1 : Fin 3))).symm
    _ = (1 : Int) := by
          simpa [relabel_profile2_eq_profile2_list] using scoreCandidate_profile2_list_1

lemma scoreCandidate_profile2_2 :
    scoreCandidate profile2 scoreVec (2 : Fin 3) = (2 : Int) := by
  calc
    scoreCandidate profile2 scoreVec (2 : Fin 3) =
        scoreCandidate (relabelProfileVoters e2 profile2) scoreVec (2 : Fin 3) := by
          simpa using
            (scoreCandidate_relabelProfileVoters (e := e2) (P := profile2)
              (score := scoreVec) (c := (2 : Fin 3))).symm
    _ = (2 : Int) := by
          simpa [relabel_profile2_eq_profile2_list] using scoreCandidate_profile2_list_2

lemma scoreCandidate_profileAll_0 :
    scoreCandidate profileAll scoreVec (0 : Fin 3) = (3 : Int) := by
  calc
    scoreCandidate profileAll scoreVec (0 : Fin 3) =
        scoreCandidate (relabelProfileVoters e4 profileAll) scoreVec (0 : Fin 3) := by
          simpa using
            (scoreCandidate_relabelProfileVoters (e := e4) (P := profileAll)
              (score := scoreVec) (c := (0 : Fin 3))).symm
    _ = (3 : Int) := by
          simpa [relabel_profileAll_eq_profileAll_list] using scoreCandidate_profileAll_list_0

lemma scoreCandidate_profileAll_1 :
    scoreCandidate profileAll scoreVec (1 : Fin 3) = (2 : Int) := by
  calc
    scoreCandidate profileAll scoreVec (1 : Fin 3) =
        scoreCandidate (relabelProfileVoters e4 profileAll) scoreVec (1 : Fin 3) := by
          simpa using
            (scoreCandidate_relabelProfileVoters (e := e4) (P := profileAll)
              (score := scoreVec) (c := (1 : Fin 3))).symm
    _ = (2 : Int) := by
          simpa [relabel_profileAll_eq_profileAll_list] using scoreCandidate_profileAll_list_1

lemma scoreCandidate_profileAll_2 :
    scoreCandidate profileAll scoreVec (2 : Fin 3) = (3 : Int) := by
  calc
    scoreCandidate profileAll scoreVec (2 : Fin 3) =
        scoreCandidate (relabelProfileVoters e4 profileAll) scoreVec (2 : Fin 3) := by
          simpa using
            (scoreCandidate_relabelProfileVoters (e := e4) (P := profileAll)
              (score := scoreVec) (c := (2 : Fin 3))).symm
    _ = (3 : Int) := by
          simpa [relabel_profileAll_eq_profileAll_list] using scoreCandidate_profileAll_list_2

lemma lowestScoring_profile1_has_2 :
    (2 : Fin 3) ∈ lowestScoring profile1 scoreVec := by
  have hA : (Finset.univ : Finset (Fin 3)).Nonempty := Finset.univ_nonempty
  apply (lowestScoring_iff_forall_le (P := profile1) (score := scoreVec) hA (2 : Fin 3)).2
  intro d
  fin_cases d <;> simp [scoreCandidate_profile1_0, scoreCandidate_profile1_1, scoreCandidate_profile1_2]

lemma lowestScoring_profile2_has_0 :
    (0 : Fin 3) ∈ lowestScoring profile2 scoreVec := by
  have hA : (Finset.univ : Finset (Fin 3)).Nonempty := Finset.univ_nonempty
  apply (lowestScoring_iff_forall_le (P := profile2) (score := scoreVec) hA (0 : Fin 3)).2
  intro d
  fin_cases d <;> simp [scoreCandidate_profile2_0, scoreCandidate_profile2_1, scoreCandidate_profile2_2]

lemma score1_lt_score0 :
    scoreCandidate profileAll scoreVec (1 : Fin 3) <
      scoreCandidate profileAll scoreVec (0 : Fin 3) := by
  simp [scoreCandidate_profileAll_1, scoreCandidate_profileAll_0]

lemma score1_lt_score2 :
    scoreCandidate profileAll scoreVec (1 : Fin 3) <
      scoreCandidate profileAll scoreVec (2 : Fin 3) := by
  simp [scoreCandidate_profileAll_1, scoreCandidate_profileAll_2]

lemma lowestScoring_profileAll_eq_singleton_1 :
    lowestScoring profileAll scoreVec = ({1} : Finset (Fin 3)) := by
  classical
  have hLne :
      (lowestScoring profileAll scoreVec).Nonempty := by
    exact lowestScoring_nonempty (P := profileAll) (score := scoreVec)
      (hA := (Finset.univ_nonempty : (Finset.univ : Finset (Fin 3)).Nonempty))
  have hsubset : lowestScoring profileAll scoreVec ⊆ ({1} : Finset (Fin 3)) := by
    intro x hx
    fin_cases x
    ·
      have hle :=
        scoreCandidate_le_of_mem_lowestScoring (P := profileAll) (score := scoreVec)
          (c := (0 : Fin 3)) (e := (1 : Fin 3)) hx
      have hcontra : False := (not_lt_of_ge hle) score1_lt_score0
      exact (False.elim hcontra)
    · simp
    ·
      have hle :=
        scoreCandidate_le_of_mem_lowestScoring (P := profileAll) (score := scoreVec)
          (c := (2 : Fin 3)) (e := (1 : Fin 3)) hx
      have hcontra : False := (not_lt_of_ge hle) score1_lt_score2
      exact (False.elim hcontra)
  rcases hLne with ⟨x, hx⟩
  have hx' : x = (1 : Fin 3) := by
    have : x ∈ ({1} : Finset (Fin 3)) := hsubset hx
    simpa using this
  have h1mem : (1 : Fin 3) ∈ lowestScoring profileAll scoreVec := by
    simpa [hx'] using hx
  apply Finset.ext
  intro x
  constructor
  · intro hxmem
    exact hsubset hxmem
  · intro hxmem
    have hx' : x = (1 : Fin 3) := by simpa using hxmem
    simpa [hx'] using h1mem

/-! ## Pairwise margins -/

lemma marginList_profile1_1_0 :
    marginList (fun v => (ballots2_1 v).ranking) (1 : Fin 3) (0 : Fin 3) = (0 : Int) := by
  decide

lemma marginList_profile2_1_2 :
    marginList (fun v => (ballots2_2 v).ranking) (1 : Fin 3) (2 : Fin 3) = (0 : Int) := by
  decide

lemma margin_profile1_1_0 :
    margin profile1 (1 : Fin 3) (0 : Fin 3) = (0 : Int) := by
  have hrel :=
    margin_relabelProfileVoters (e := e1) (P := profile1) (a := (1 : Fin 3)) (b := (0 : Fin 3))
  have hlist :
      margin (relabelProfileVoters e1 profile1) (1 : Fin 3) (0 : Fin 3) =
        marginList (fun v => (ballots2_1 v).ranking) (1 : Fin 3) (0 : Fin 3) := by
    simpa [relabel_profile1_eq_profile1_list, profile1_list] using
      (margin_eq_marginList (ballots := ballots2_1) (a := (1 : Fin 3)) (b := (0 : Fin 3)))
  calc
    margin profile1 (1 : Fin 3) (0 : Fin 3) =
        margin (relabelProfileVoters e1 profile1) (1 : Fin 3) (0 : Fin 3) := by
          symm
          exact hrel
    _ = marginList (fun v => (ballots2_1 v).ranking) (1 : Fin 3) (0 : Fin 3) := hlist
    _ = (0 : Int) := marginList_profile1_1_0

lemma margin_profile2_1_2 :
    margin profile2 (1 : Fin 3) (2 : Fin 3) = (0 : Int) := by
  have hrel :=
    margin_relabelProfileVoters (e := e2) (P := profile2) (a := (1 : Fin 3)) (b := (2 : Fin 3))
  have hlist :
      margin (relabelProfileVoters e2 profile2) (1 : Fin 3) (2 : Fin 3) =
        marginList (fun v => (ballots2_2 v).ranking) (1 : Fin 3) (2 : Fin 3) := by
    simpa [relabel_profile2_eq_profile2_list, profile2_list] using
      (margin_eq_marginList (ballots := ballots2_2) (a := (1 : Fin 3)) (b := (2 : Fin 3)))
  calc
    margin profile2 (1 : Fin 3) (2 : Fin 3) =
        margin (relabelProfileVoters e2 profile2) (1 : Fin 3) (2 : Fin 3) := by
          symm
          exact hrel
    _ = marginList (fun v => (ballots2_2 v).ranking) (1 : Fin 3) (2 : Fin 3) := hlist
    _ = (0 : Int) := marginList_profile2_1_2

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
