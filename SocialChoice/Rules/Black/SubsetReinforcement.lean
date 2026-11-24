import Mathlib.Tactic
import Mathlib.Tactic.FinCases
import SocialChoice.Axioms.Participation
import SocialChoice.ListBallot
import SocialChoice.Rules.Black.Condorcet

namespace SocialChoice

open Finset

/-!
## Black fails subset reinforcement

Counterexample with 3 candidates and two disjoint electorates:

Subprofile 1 (3 voters):
  0 > 2 > 1
  1 > 0 > 2
  2 > 1 > 0
Black selects all candidates.

Subprofile 2 (2 voters):
  1 > 2 > 0
  2 > 1 > 0
Black selects {1,2}.

Full profile (5 voters):
  0 > 2 > 1
  1 > 0 > 2
  1 > 2 > 0
  2 > 1 > 0
  2 > 1 > 0
Black selects {2}.

Thus 1 is a winner in both subprofiles but not in the full profile.
-/

namespace BlackSubsetReinforcementCounterexample

def ballot021 : ListBallot 3 := ListBallot.mk' [0, 2, 1]
def ballot102 : ListBallot 3 := ListBallot.mk' [1, 0, 2]
def ballot120 : ListBallot 3 := ListBallot.mk' [1, 2, 0]
def ballot210 : ListBallot 3 := ListBallot.mk' [2, 1, 0]

def ballots5 : Fin 5 → ListBallot 3
  | 0 => ballot021
  | 1 => ballot102
  | 2 => ballot210
  | 3 => ballot120
  | 4 => ballot210
  | _ => ballot210

def voters3 : Finset (Fin 5) :=
  (Finset.univ.filter fun v => v.val < 3)

def voters2 : Finset (Fin 5) :=
  (Finset.univ.filter fun v => 3 ≤ v.val)

def ballots3 (v : Electorate (Fin 5) voters3) : ListBallot 3 := ballots5 v.1
def ballots2 (v : Electorate (Fin 5) voters2) : ListBallot 3 := ballots5 v.1
def ballotsAll (v : Electorate (Fin 5) (voters3 ∪ voters2)) : ListBallot 3 := ballots5 v.1

noncomputable def profile3 : Profile (Electorate (Fin 5) voters3) (Fin 3) :=
  profileOfListBallots ballots3

noncomputable def profile2 : Profile (Electorate (Fin 5) voters2) (Fin 3) :=
  profileOfListBallots ballots2

noncomputable def profileAll :
    Profile (Electorate (Fin 5) (voters3 ∪ voters2)) (Fin 3) :=
  profileOfListBallots ballotsAll

lemma voters3_disjoint_voters2 : Disjoint voters3 voters2 := by
  classical
  refine Finset.disjoint_left.2 ?_
  intro x hx3 hx2
  have hx3' : x.val < 3 := (Finset.mem_filter.mp hx3).2
  have hx2' : 3 ≤ x.val := (Finset.mem_filter.mp hx2).2
  linarith

lemma voters3_eq : voters3 = ({0, 1, 2} : Finset (Fin 5)) := by
  ext v
  fin_cases v <;> simp [voters3]

lemma voters2_eq : voters2 = ({3, 4} : Finset (Fin 5)) := by
  ext v
  fin_cases v <;> simp [voters2]

lemma votersAll_eq : voters3 ∪ voters2 = (Finset.univ : Finset (Fin 5)) := by
  ext v
  fin_cases v <;> simp [voters3, voters2]

lemma card_voters3 : Fintype.card (Electorate (Fin 5) voters3) = 3 := by
  classical
  simpa [Electorate, voters3_eq] using (Fintype.card_coe (s := voters3))

lemma card_voters2 : Fintype.card (Electorate (Fin 5) voters2) = 2 := by
  classical
  simpa [Electorate, voters2_eq] using (Fintype.card_coe (s := voters2))

lemma card_votersAll : Fintype.card (Electorate (Fin 5) (voters3 ∪ voters2)) = 5 := by
  classical
  simp [Electorate, votersAll_eq]

lemma restrict_profileAll_voters3 :
    restrictElectorate profileAll voters3
        (by intro x hx; exact Finset.mem_union.mpr (Or.inl hx)) =
      profile3 := by
  unfold profileAll profile3 ballotsAll ballots3
  rfl

lemma restrict_profileAll_voters2 :
    restrictElectorate profileAll voters2
        (by intro x hx; exact Finset.mem_union.mpr (Or.inr hx)) =
      profile2 := by
  unfold profileAll profile2 ballotsAll ballots2
  rfl

lemma no_condorcet_profile3 : ¬ ∃ x, CondorcetWinner profile3 x := by
  simp only [CondorcetWinner_iff_margin_pos, margin_pos, profile3, margin_profileOfListBallots]
  decide

lemma no_condorcet_profile2 : ¬ ∃ x, CondorcetWinner profile2 x := by
  simp only [CondorcetWinner_iff_margin_pos, margin_pos, profile2, margin_profileOfListBallots]
  decide

lemma condorcet_profileAll : CondorcetWinner profileAll (2 : Fin 3) := by
  simp only [CondorcetWinner_iff_margin_pos, margin_pos, profileAll, margin_profileOfListBallots]
  decide

lemma borda_profile3 : borda profile3 = (Finset.univ : Finset (Fin 3)) := by
  apply Finset.eq_univ_of_forall
  intro x
  fin_cases x <;> decide

lemma borda_profile2 : borda profile2 = ({1, 2} : Finset (Fin 3)) := by
  ext x
  fin_cases x <;> decide

lemma black_profile3 : black profile3 = (Finset.univ : Finset (Fin 3)) := by
  have h : ¬ ∃ x, CondorcetWinner profile3 x := no_condorcet_profile3
  simpa [black, h] using borda_profile3

lemma black_profile2 : black profile2 = ({1, 2} : Finset (Fin 3)) := by
  have h : ¬ ∃ x, CondorcetWinner profile2 x := no_condorcet_profile2
  simpa [black, h] using borda_profile2

lemma black_profileAll : black profileAll = ({2} : Finset (Fin 3)) := by
  exact black_condorcet_consistency (P := profileAll) (c := (2 : Fin 3))
    condorcet_profileAll

theorem black_subsetReinforcement_counterexample_sets :
    ¬ (black profile3 ∩ black profile2 ⊆ black profileAll) := by
  intro hsubset
  have h1 : (1 : Fin 3) ∈ black profile3 ∩ black profile2 := by
    simp [black_profile3, black_profile2]
  have h1' : (1 : Fin 3) ∈ black profileAll := hsubset h1
  have hfalse : False := by
    simp [black_profileAll] at h1'
  exact hfalse

end BlackSubsetReinforcementCounterexample

end SocialChoice
