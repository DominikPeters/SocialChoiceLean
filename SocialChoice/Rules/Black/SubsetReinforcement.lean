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

section BallotHelpers

variable {V : Type} [Fintype V]

noncomputable def profileOfBallots (ballots : V → ListBallot 3) : Profile V (Fin 3) :=
  { pref := fun v => (ballots v).toLinearOrder }

lemma prefers_iff_prefersInList' (ballots : V → ListBallot 3) (v : V) (a b : Fin 3) :
    Prefers (profileOfBallots ballots) v a b ↔ prefersInList (ballots v).ranking a b = true := by
  unfold Prefers profileOfBallots prefersInList
  rw [(ballots v).lt_iff_idxOf]
  simp only [decide_eq_true_eq]

end BallotHelpers

def voters3 : Finset (Fin 5) :=
  (Finset.univ.filter fun v => v.val < 3)

def voters2 : Finset (Fin 5) :=
  (Finset.univ.filter fun v => 3 ≤ v.val)

def ballots3 (v : Electorate (Fin 5) voters3) : ListBallot 3 := ballots5 v.1
def ballots2 (v : Electorate (Fin 5) voters2) : ListBallot 3 := ballots5 v.1
def ballotsAll (v : Electorate (Fin 5) (voters3 ∪ voters2)) : ListBallot 3 := ballots5 v.1

noncomputable def profile3 : Profile (Electorate (Fin 5) voters3) (Fin 3) :=
  profileOfBallots ballots3

noncomputable def profile2 : Profile (Electorate (Fin 5) voters2) (Fin 3) :=
  profileOfBallots ballots2

noncomputable def profileAll :
    Profile (Electorate (Fin 5) (voters3 ∪ voters2)) (Fin 3) :=
  profileOfBallots ballotsAll

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

def v0_3 : Electorate (Fin 5) voters3 := ⟨0, by simp [voters3]⟩
def v1_3 : Electorate (Fin 5) voters3 := ⟨1, by simp [voters3]⟩
def v2_3 : Electorate (Fin 5) voters3 := ⟨2, by simp [voters3]⟩

def v3_2 : Electorate (Fin 5) voters2 := ⟨3, by simp [voters2]⟩
def v4_2 : Electorate (Fin 5) voters2 := ⟨4, by simp [voters2]⟩

def v0_all : Electorate (Fin 5) (voters3 ∪ voters2) := ⟨0, by simp [voters3, voters2]⟩
def v1_all : Electorate (Fin 5) (voters3 ∪ voters2) := ⟨1, by simp [voters3, voters2]⟩
def v2_all : Electorate (Fin 5) (voters3 ∪ voters2) := ⟨2, by simp [voters3, voters2]⟩
def v3_all : Electorate (Fin 5) (voters3 ∪ voters2) := ⟨3, by simp [voters3, voters2]⟩
def v4_all : Electorate (Fin 5) (voters3 ∪ voters2) := ⟨4, by simp [voters3, voters2]⟩

lemma votersPreferring_profile3_0_1 :
    votersPreferring profile3 (0 : Fin 3) (1 : Fin 3) = {v0_3} := by
  classical
  ext v
  cases v with
  | mk val hmem =>
      fin_cases val
      ·
        simp [votersPreferring, profile3, ballots3, ballots5, voters3,
          prefers_iff_prefersInList', v0_3]; decide +revert
      ·
        simp [votersPreferring, profile3, ballots3, ballots5, voters3,
          prefers_iff_prefersInList', v0_3]; decide +revert
      ·
        simp [votersPreferring, profile3, ballots3, ballots5, voters3,
          prefers_iff_prefersInList', v0_3]; decide +revert
      ·
        simp [voters3] at hmem
      ·
        simp [voters3] at hmem

lemma votersPreferring_profile3_1_2 :
    votersPreferring profile3 (1 : Fin 3) (2 : Fin 3) = {v1_3} := by
  classical
  ext v
  cases v with
  | mk val hmem =>
      fin_cases val
      ·
        simp [votersPreferring, profile3, ballots3, ballots5, voters3,
          prefers_iff_prefersInList', v1_3]; decide +revert
      ·
        simp [votersPreferring, profile3, ballots3, ballots5, voters3,
          prefers_iff_prefersInList', v1_3]; decide +revert
      ·
        simp [votersPreferring, profile3, ballots3, ballots5, voters3,
          prefers_iff_prefersInList', v1_3]; decide +revert
      ·
        simp [voters3] at hmem
      ·
        simp [voters3] at hmem

lemma votersPreferring_profile3_2_0 :
    votersPreferring profile3 (2 : Fin 3) (0 : Fin 3) = {v2_3} := by
  classical
  ext v
  cases v with
  | mk val hmem =>
      fin_cases val
      ·
        simp [votersPreferring, profile3, ballots3, ballots5, voters3,
          prefers_iff_prefersInList', v2_3]; decide +revert
      ·
        simp [votersPreferring, profile3, ballots3, ballots5, voters3,
          prefers_iff_prefersInList', v2_3]; decide +revert
      ·
        simp [votersPreferring, profile3, ballots3, ballots5, voters3,
          prefers_iff_prefersInList', v2_3]; decide +revert
      ·
        simp [voters3] at hmem
      ·
        simp [voters3] at hmem

lemma votersPreferring_profile2_0_1 :
    votersPreferring profile2 (0 : Fin 3) (1 : Fin 3) =
      (∅ : Finset (Electorate (Fin 5) voters2)) := by
  classical
  ext v
  cases v with
  | mk val hmem =>
      fin_cases val
      ·
        simp [voters2] at hmem
      ·
        simp [voters2] at hmem
      ·
        simp [voters2] at hmem
      ·
        simp [votersPreferring, profile2, ballots2, ballots5, voters2,
          prefers_iff_prefersInList']; decide +revert
      ·
        simp [votersPreferring, profile2, ballots2, ballots5, voters2,
          prefers_iff_prefersInList']; decide +revert

lemma votersPreferring_profile2_1_2 :
    votersPreferring profile2 (1 : Fin 3) (2 : Fin 3) = {v3_2} := by
  classical
  ext v
  cases v with
  | mk val hmem =>
      fin_cases val
      ·
        simp [voters2] at hmem
      ·
        simp [voters2] at hmem
      ·
        simp [voters2] at hmem
      ·
        simp [votersPreferring, profile2, ballots2, ballots5, voters2,
          prefers_iff_prefersInList', v3_2]; decide +revert
      ·
        simp [votersPreferring, profile2, ballots2, ballots5, voters2,
          prefers_iff_prefersInList', v3_2]; decide +revert

lemma votersPreferring_profile2_2_1 :
    votersPreferring profile2 (2 : Fin 3) (1 : Fin 3) = {v4_2} := by
  classical
  ext v
  cases v with
  | mk val hmem =>
      fin_cases val
      ·
        simp [voters2] at hmem
      ·
        simp [voters2] at hmem
      ·
        simp [voters2] at hmem
      ·
        simp [votersPreferring, profile2, ballots2, ballots5, voters2,
          prefers_iff_prefersInList', v4_2]; decide +revert
      ·
        simp [votersPreferring, profile2, ballots2, ballots5, voters2,
          prefers_iff_prefersInList', v4_2]; decide +revert

lemma votersPreferring_profileAll_2_0 :
    votersPreferring profileAll (2 : Fin 3) (0 : Fin 3) = {v2_all, v3_all, v4_all} := by
  classical
  ext v
  cases v with
  | mk val hmem =>
      fin_cases val <;>
        (simp [votersPreferring, profileAll, ballotsAll, ballots5,
          voters3, voters2, prefers_iff_prefersInList', v2_all, v3_all, v4_all]; decide +revert)

lemma votersPreferring_profileAll_2_1 :
    votersPreferring profileAll (2 : Fin 3) (1 : Fin 3) = {v0_all, v2_all, v4_all} := by
  classical
  ext v
  cases v with
  | mk val hmem =>
      fin_cases val <;>
        (simp [votersPreferring, profileAll, ballotsAll, ballots5,
          voters3, voters2, prefers_iff_prefersInList', v0_all, v2_all, v4_all]; decide +revert)

lemma not_strictMajority_profile3_0_1 :
    ¬ StrictMajority (votersPreferring profile3 (0 : Fin 3) (1 : Fin 3)) := by
  simp [StrictMajority, votersPreferring_profile3_0_1]; decide +revert

lemma not_strictMajority_profile3_1_2 :
    ¬ StrictMajority (votersPreferring profile3 (1 : Fin 3) (2 : Fin 3)) := by
  simp [StrictMajority, votersPreferring_profile3_1_2]; decide +revert

lemma not_strictMajority_profile3_2_0 :
    ¬ StrictMajority (votersPreferring profile3 (2 : Fin 3) (0 : Fin 3)) := by
  simp [StrictMajority, votersPreferring_profile3_2_0]; decide +revert

lemma not_strictMajority_profile2_0_1 :
    ¬ StrictMajority (votersPreferring profile2 (0 : Fin 3) (1 : Fin 3)) := by
  simp [StrictMajority, votersPreferring_profile2_0_1]

lemma not_strictMajority_profile2_1_2 :
    ¬ StrictMajority (votersPreferring profile2 (1 : Fin 3) (2 : Fin 3)) := by
  simp [StrictMajority, votersPreferring_profile2_1_2]; decide +revert

lemma not_strictMajority_profile2_2_1 :
    ¬ StrictMajority (votersPreferring profile2 (2 : Fin 3) (1 : Fin 3)) := by
  simp [StrictMajority, votersPreferring_profile2_2_1]; decide +revert

lemma strictMajority_profileAll_2_0 :
    StrictMajority (votersPreferring profileAll (2 : Fin 3) (0 : Fin 3)) := by
  simp [StrictMajority, votersPreferring_profileAll_2_0]; decide +revert

lemma strictMajority_profileAll_2_1 :
    StrictMajority (votersPreferring profileAll (2 : Fin 3) (1 : Fin 3)) := by
  simp [StrictMajority, votersPreferring_profileAll_2_1]; decide +revert

lemma no_condorcet_profile3 : ¬ ∃ x, CondorcetWinner profile3 x := by
  intro h
  rcases h with ⟨x, hx⟩
  fin_cases x
  · have hmaj := hx (1 : Fin 3) (by decide)
    exact (not_strictMajority_profile3_0_1 hmaj).elim
  · have hmaj := hx (2 : Fin 3) (by decide)
    exact (not_strictMajority_profile3_1_2 hmaj).elim
  · have hmaj := hx (0 : Fin 3) (by decide)
    exact (not_strictMajority_profile3_2_0 hmaj).elim

lemma no_condorcet_profile2 : ¬ ∃ x, CondorcetWinner profile2 x := by
  intro h
  rcases h with ⟨x, hx⟩
  fin_cases x
  · have hmaj := hx (1 : Fin 3) (by decide)
    exact (not_strictMajority_profile2_0_1 hmaj).elim
  · have hmaj := hx (2 : Fin 3) (by decide)
    exact (not_strictMajority_profile2_1_2 hmaj).elim
  · have hmaj := hx (1 : Fin 3) (by decide)
    exact (not_strictMajority_profile2_2_1 hmaj).elim

lemma condorcet_profileAll : CondorcetWinner profileAll (2 : Fin 3) := by
  intro d hne
  fin_cases d
  · have hmaj := strictMajority_profileAll_2_0
    simpa using hmaj
  · have hmaj := strictMajority_profileAll_2_1
    simpa using hmaj
  · cases hne rfl

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
